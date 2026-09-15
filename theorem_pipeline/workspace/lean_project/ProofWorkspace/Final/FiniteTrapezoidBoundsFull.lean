import ProofWorkspace.Final.XiGridTailFull
import ProofWorkspace.Final.DensityAliasBoundsFull
import ProofWorkspace.Final.QuadratureBudgetFull

/-!
# Actual finite reciprocal-Xi Fourier quadrature

The actual sampled tail has a geometric majorant. At mesh 1/40 and cutoff
13600 this uses less than half of 10^-85, with no sample-value assumptions.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace ReciprocalXi

def finiteTrapezoid (z : ℂ) (h : ℝ) (K : ℕ) : ℂ :=
  (h / (2 * Real.pi)) •
    ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), quadratureInput z h (n : ℝ)

theorem int_mem_symmetric_Icc_iff (n : ℤ) (K : ℕ) :
    n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ↔ n.natAbs ≤ K := by
  rw [Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs]
  exact Nat.cast_le

theorem hasSum_int_cutoff_geometric (rho : ℝ) (K : ℕ)
    (hr0 : 0 ≤ rho) (hr1 : rho < 1) :
    HasSum (fun n : ℤ => if K < n.natAbs then rho ^ (n.natAbs - K) else 0)
      (2 * rho / (1 - rho)) := by
  let f : ℕ → ℝ := fun n => if K < n + 1 then rho ^ (n + 1 - K) else 0
  have hg : HasSum (fun n : ℕ => rho ^ (n + 1)) (rho / (1 - rho)) := by
    convert (hasSum_geometric_of_lt_one hr0 hr1).mul_right rho using 1
    ring
  have hs : HasSum (fun n : ℕ => f (n + K)) (rho / (1 - rho)) := by
    convert hg using 1
    funext n
    simp only [f, if_pos (show K < n + K + 1 by omega)]
    congr 1
    omega
  have hz : ∑ n ∈ Finset.range K, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact if_neg (by have h := Finset.mem_range.mp hn; omega)
  have hp : HasSum f (rho / (1 - rho)) := by
    have h := hs.sum_range_add
    rw [hz, zero_add] at h
    exact h
  have hp' : HasSum (fun n : ℕ => if K < ((n : ℤ) + 1).natAbs then
      rho ^ (((n : ℤ) + 1).natAbs - K) else 0) (rho / (1 - rho)) := by
    simpa only [← Int.natCast_succ, Int.natAbs_natCast] using hp
  have hn' : HasSum (fun n : ℕ => if K < (-((n : ℤ) + 1)).natAbs then
      rho ^ ((-((n : ℤ) + 1)).natAbs - K) else 0) (rho / (1 - rho)) := by
    simpa only [Int.natAbs_neg] using hp'
  have h := HasSum.of_add_one_of_neg_add_one
    (f := fun n : ℤ => if K < n.natAbs then rho ^ (n.natAbs - K) else 0) hp' hn'
  simp only [Int.natAbs_zero, Nat.not_lt_zero, if_false] at h
  convert h using 1
  ring

theorem hasSum_int_cutoff_exp (a : ℝ) (K : ℕ) (ha : 0 < a) :
    HasSum (fun n : ℤ => if K < n.natAbs then
      Real.exp (-a * ((n.natAbs - K : ℕ) : ℝ)) else 0)
      (2 / (Real.exp a - 1)) := by
  have hr : Real.exp (-a) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_neg_of_pos ha)
  have h := hasSum_int_cutoff_geometric (Real.exp (-a)) K (Real.exp_pos _).le hr
  have he (n : ℕ) : (Real.exp (-a)) ^ n = Real.exp (-a * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he] at h
  convert h using 1
  rw [Real.exp_neg]
  have hne : Real.exp a ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp

/-- A sampled tail term is controlled by the actual grid-tail theorem. -/
theorem quadratureInput_cutoff_norm_le (z : ℂ) (h q : ℝ) (K : ℕ) (n : ℤ)
    (hh : 0 < h) (hK : 340 ≤ h * (K : ℝ)) (hq : |z.im| ≤ q) (hn : K < n.natAbs) :
    ‖quadratureInput z h (n : ℝ)‖ ≤
      Real.exp (-200 + q * h * K) *
        Real.exp (-((4 / 5 - q) * h) * ((n.natAbs - K : ℕ) : ℝ)) := by
  have hnabs : (n.natAbs : ℝ) = |(n : ℝ)| := by
    have ht := congrArg (fun k : ℤ => (k : ℝ)) (Int.natCast_natAbs n)
    simpa only [Int.cast_natCast, Int.cast_abs] using ht
  have hKn : (K : ℝ) ≤ n.natAbs := by exact_mod_cast hn.le
  have hhu : |h * (n : ℝ)| = h * (n.natAbs : ℝ) := by
    rw [abs_mul, abs_of_pos hh, ← hnabs]
  have hu : 340 ≤ |h * (n : ℝ)| := by
    rw [hhu]
    exact hK.trans (mul_le_mul_of_nonneg_left hKn hh.le)
  have hp := reciprocalTransform_grid_tail (h * (n : ℝ)) hu
  have he : ‖Complex.exp (-Complex.I * z * ((h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      Real.exp (q * |h * (n : ℝ)|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hid : (-Complex.I * z * ((h * (n : ℝ) : ℝ) : ℂ)).re = z.im * (h * (n : ℝ)) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hid]
    calc
      _ ≤ |z.im * (h * (n : ℝ))| := le_abs_self _
      _ = |z.im| * |h * (n : ℝ)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hq (abs_nonneg _)
  unfold quadratureInput
  rw [norm_mul]
  apply (mul_le_mul hp he (norm_nonneg _) (by positivity)).trans
  have hsub : ((n.natAbs - K : ℕ) : ℝ) = (n.natAbs : ℝ) - K :=
    Nat.cast_sub hn.le
  rw [hhu, hsub]
  repeat rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Finite truncation of the actual Fourier samples, retaining both endpoints
−K and K. Its omitted terms start at K+1 in each direction. -/
theorem infiniteTrapezoid_sub_finite_norm_le (z : ℂ) (h q : ℝ) (K : ℕ)
    (hh : 0 < h) (hK : 340 ≤ h * (K : ℝ)) (hq : |z.im| ≤ q) (hq4 : q < 4 / 5) :
    ‖infiniteTrapezoid z h - finiteTrapezoid z h K‖ ≤
      (h / Real.pi) * Real.exp (-200 + q * h * K) /
        (Real.exp ((4 / 5 - q) * h) - 1) := by
  let f : ℤ → ℂ := fun n => quadratureInput z h (n : ℝ)
  let S : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hhead : HasSum (fun n : ℤ => if n ∈ S then f n else 0) (∑ n ∈ S, f n) := by
    have ht : HasSum (fun n : ℤ => if n ∈ S then f n else 0)
        (∑ n ∈ S, if n ∈ S then f n else 0) := hasSum_sum_of_ne_finset_zero (s := S)
      (f := fun n : ℤ => if n ∈ S then f n else 0)
      (by intro n hn; exact if_neg hn)
    convert ht using 1
    apply Finset.sum_congr rfl
    intro n hn
    exact (if_pos hn).symm
  have htail : HasSum (fun n : ℤ => if K < n.natAbs then f n else 0)
      ((∑' n : ℤ, f n) - ∑ n ∈ S, f n) := by
    convert (summable_quadratureInput z h hh).hasSum.sub hhead using 1
    funext n
    have hi : n ∈ S ↔ n.natAbs ≤ K := int_mem_symmetric_Icc_iff n K
    by_cases hn : K < n.natAbs
    · simp only [if_pos hn, hi, if_neg (not_le.mpr hn), sub_zero, f]
    · simp only [if_neg hn, hi, if_pos (le_of_not_gt hn), sub_self, f]
  have ha : 0 < (4 / 5 - q) * h := mul_pos (sub_pos.mpr hq4) hh
  have hm : HasSum (fun n : ℤ => if K < n.natAbs then
      Real.exp (-200 + q * h * K) *
        Real.exp (-((4 / 5 - q) * h) * ((n.natAbs - K : ℕ) : ℝ)) else 0)
      (2 * Real.exp (-200 + q * h * K) / (Real.exp ((4 / 5 - q) * h) - 1)) := by
    have ht := (hasSum_int_cutoff_exp ((4 / 5 - q) * h) K ha).mul_left
      (Real.exp (-200 + q * h * K))
    convert ht using 1
    · funext n
      split_ifs <;> simp
    · ring
  have hb := htail.norm_le_of_bounded hm (fun n => by
    by_cases hn : K < n.natAbs
    · simp only [if_pos hn]
      exact quadratureInput_cutoff_norm_le z h q K n hh hK hq hn
    · simp only [if_neg hn, norm_zero, le_refl])
  unfold infiniteTrapezoid finiteTrapezoid
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ h / (2 * Real.pi))]
  have hscaled := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ h / (2 * Real.pi))
  convert hscaled using 1
  ring

theorem finiteTrapezoid_total_error_le (z : ℂ) (h q : ℝ) (K : ℕ)
    (hh : 0 < h) (hK : 340 ≤ h * (K : ℝ)) (hq : |z.im| ≤ q) (hq4 : q < 4 / 5) :
    ‖finiteTrapezoid z h K - complexDensity z‖ ≤
      (h / Real.pi) * Real.exp (-200 + q * h * K) /
        (Real.exp ((4 / 5 - q) * h) - 1) +
      2 * densityAliasAmplitude z / (Real.exp (2 * Real.pi / h) - 1) := by
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (finiteTrapezoid z h K) (infiniteTrapezoid z h) (complexDensity z)
  have ht := infiniteTrapezoid_sub_finite_norm_le z h q K hh hK hq hq4
  have ha := infiniteTrapezoid_error_le z h hh
  rw [norm_sub_rev (finiteTrapezoid z h K) (infiniteTrapezoid z h)] at htriangle
  linarith

theorem exp_neg_983_fifths_lt_ten_pow_neg85 :
    Real.exp (-(983 / 5 : ℝ)) < 1 / (10 : ℝ) ^ 85 := by
  have hl := (ratExp_scaled_enclosure (231 / 100) 3 12 (by norm_num) (by norm_num)
    (by norm_num)).1
  have hnum : (10 : ℝ) ≤ (ratExpScaledLower (231 / 100) 3 12 : ℝ) := by
    norm_num [ratExpScaledLower, ratExpTaylor, ratExpError,
      Finset.sum_range_succ, Nat.factorial]
  have h10 : (10 : ℝ) ≤ Real.exp (231 / 100) := by simpa using hnum.trans hl
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) h10 85
  rw [← Real.exp_nat_mul] at hp
  have hb : (10 : ℝ) ^ 85 < Real.exp (983 / 5) :=
    hp.trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  simpa only [one_div, ← Real.exp_neg] using
    one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 10 ^ 85) hb

/-- Actual sampled Fourier tails at the source mesh and cutoff consume less
than one half of 10^-85; no sampled values are assumed or supplied here. -/
theorem infiniteTrapezoid_sub_finite_grid_lt (z : ℂ) (hi : |z.im| ≤ 1 / 100) :
    ‖infiniteTrapezoid z (1 / 40) - finiteTrapezoid z (1 / 40) 13600‖ <
      1 / (2 * (10 : ℝ) ^ 85) := by
  have ht := infiniteTrapezoid_sub_finite_norm_le z (1 / 40) (1 / 100) 13600
    (by norm_num) (by norm_num) hi (by norm_num)
  norm_num at ht
  have hd : (79 / 4000 : ℝ) ≤ Real.exp (79 / 4000) - 1 := by
    linarith [Real.add_one_le_exp (79 / 4000 : ℝ)]
  have hp : (1 / 40 : ℝ) / Real.pi ≤ 1 / 120 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  have he0 : 0 ≤ Real.exp (-(983 / 5 : ℝ)) := (Real.exp_pos _).le
  have hb : ((1 / 40 : ℝ) / Real.pi) * Real.exp (-(983 / 5 : ℝ)) /
      (Real.exp (79 / 4000) - 1) ≤
      (100 / 237 : ℝ) * Real.exp (-(983 / 5 : ℝ)) := by
    calc
      _ ≤ ((1 / 120 : ℝ) * Real.exp (-(983 / 5 : ℝ))) / (79 / 4000) :=
        div_le_div₀ (mul_nonneg (by norm_num) he0)
          (mul_le_mul_of_nonneg_right hp he0) (by norm_num) hd
      _ = _ := by ring
  have hb' : ‖infiniteTrapezoid z (1 / 40) - finiteTrapezoid z (1 / 40) 13600‖ ≤
      (100 / 237 : ℝ) * Real.exp (-(983 / 5 : ℝ)) := by
    apply le_trans ht
    convert hb using 1
  calc
    _ ≤ _ := hb'
    _ < (100 / 237 : ℝ) * (1 / (10 : ℝ) ^ 85) :=
      mul_lt_mul_of_pos_left exp_neg_983_fifths_lt_ten_pow_neg85 (by norm_num)
    _ < 1 / (2 * (10 : ℝ) ^ 85) := by norm_num

theorem finiteTrapezoid_error_grid_lt (z : ℂ)
    (hr : |z.re| ≤ 4) (hi : |z.im| ≤ 1 / 100) :
    ‖finiteTrapezoid z (1 / 40) 13600 - complexDensity z‖ <
      3 / (4 * (10 : ℝ) ^ 85) := by
  have ht := infiniteTrapezoid_sub_finite_grid_lt z hi
  have ha := infiniteTrapezoid_error_grid_lt z hr hi
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (finiteTrapezoid z (1 / 40) 13600) (infiniteTrapezoid z (1 / 40)) (complexDensity z)
  rw [norm_sub_rev (finiteTrapezoid z (1 / 40) 13600)
    (infiniteTrapezoid z (1 / 40))] at htriangle
  linarith

end ReciprocalXi
