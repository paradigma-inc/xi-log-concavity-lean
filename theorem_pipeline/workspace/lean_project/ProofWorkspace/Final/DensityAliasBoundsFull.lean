import ProofWorkspace.Final.ComplexDensityFull
import ProofWorkspace.Final.ShiftedFourierFull
import ProofWorkspace.Final.XiPoissonFull
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual density aliases and their quantitative tail

The actual contour-shift decay is summed over both directions of the integer
lattice. Neither decay nor absolute summability is an extra premise.
-/

noncomputable section
open MeasureTheory Filter
namespace ReciprocalXi

def densityAliasAmplitude (z : ℂ) : ℝ :=
  (5 * Real.exp |z.re|) / (2 * Real.pi) *
    ∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖

theorem densityAliasAmplitude_nonneg (z : ℂ) : 0 ≤ densityAliasAmplitude z := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun u => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))

theorem complexDensity_norm_le_exp (z : ℂ) :
    ‖complexDensity z‖ ≤ (5 * Real.exp (-|z.re|)) / (2 * Real.pi) *
      ∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖ := by
  unfold complexDensity
  rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
  have h := div_le_div_of_nonneg_right (inverseFourierIntegral_norm_le_exp z)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  convert h using 1
  ring

/-- Every integer translate is dominated by a geometric lattice weight. -/
theorem complexDensity_shift_norm_le (z : ℂ) (L : ℝ) (hL : 0 < L) (n : ℤ) :
    ‖complexDensity (z + (L : ℂ) * (n : ℂ))‖ ≤
      densityAliasAmplitude z * Real.exp (-L * |(n : ℝ)|) := by
  have h := complexDensity_norm_le_exp (z + (L : ℂ) * (n : ℂ))
  have hre : (z + (L : ℂ) * (n : ℂ)).re = z.re + L * (n : ℝ) := by simp
  have him : (z + (L : ℂ) * (n : ℂ)).im = z.im := by simp
  rw [hre, him] at h
  have ha : -|z.re + L * (n : ℝ)| ≤ |z.re| - L * |(n : ℝ)| := by
    have hh := abs_add_le (z.re + L * (n : ℝ)) (-z.re)
    rw [show z.re + L * (n : ℝ) + -z.re = L * (n : ℝ) by ring,
      abs_mul, abs_of_pos hL, abs_neg] at hh
    linarith
  apply h.trans
  have hi : 0 ≤ ∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖ :=
    integral_nonneg (fun u => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  calc
    _ ≤ (5 * Real.exp (|z.re| - L * |(n : ℝ)|)) / (2 * Real.pi) *
        ∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖ := by gcongr
    _ = _ := by
      unfold densityAliasAmplitude
      rw [sub_eq_add_neg, Real.exp_add, ← neg_mul]
      ring

theorem summable_int_natAbs_geometric (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℤ => q ^ n.natAbs) := by
  have h := (hasSum_geometric_of_lt_one hq0 hq1).summable
  apply Summable.of_nat_of_neg_add_one
  · simpa only [Int.natAbs_natCast] using h
  · simpa only [Int.natAbs_neg, ← Int.natCast_succ, Int.natAbs_natCast] using
      (summable_nat_add_iff 1).mpr h

theorem hasSum_int_nonzero_natAbs_geometric (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => if n = 0 then 0 else q ^ n.natAbs)
      (2 * q / (1 - q)) := by
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_right q
  have hsucc : HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
    convert hgeo using 1
    ring
  have hp : HasSum (fun n : ℕ =>
      if (n : ℤ) + 1 = 0 then 0 else q ^ ((n : ℤ) + 1).natAbs)
      (q / (1 - q)) := by
    simpa only [← Int.natCast_succ, Int.natCast_eq_zero, Nat.succ_ne_zero,
      if_false, Int.natAbs_natCast] using hsucc
  have hn : HasSum (fun n : ℕ =>
      if -((n : ℤ) + 1) = 0 then 0 else q ^ (-((n : ℤ) + 1)).natAbs)
      (q / (1 - q)) := by
    simpa only [neg_eq_zero, Int.natAbs_neg] using hp
  have hh := HasSum.of_add_one_of_neg_add_one
    (f := fun n : ℤ => if n = 0 then 0 else q ^ n.natAbs) hp hn
  change HasSum (fun n : ℤ => if n = 0 then 0 else q ^ n.natAbs)
    (q / (1 - q) + 0 + q / (1 - q)) at hh
  convert hh using 1
  ring

theorem exp_int_abs_eq_natAbs_pow (L : ℝ) (n : ℤ) :
    Real.exp (-L * |(n : ℝ)|) = (Real.exp (-L)) ^ n.natAbs := by
  rw [← Real.exp_nat_mul]
  congr 1
  have hn : (n.natAbs : ℝ) = |(n : ℝ)| := by
    have h := congrArg (fun k : ℤ => (k : ℝ)) (Int.natCast_natAbs n)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  rw [hn]
  ring

theorem summable_int_exp_abs (L : ℝ) (hL : 0 < L) :
    Summable (fun n : ℤ => Real.exp (-L * |(n : ℝ)|)) := by
  simp_rw [exp_int_abs_eq_natAbs_pow]
  exact summable_int_natAbs_geometric _ (Real.exp_pos _).le
    (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_neg_of_pos hL))

theorem hasSum_int_nonzero_exp_abs (L : ℝ) (hL : 0 < L) :
    HasSum (fun n : ℤ => if n = 0 then 0 else Real.exp (-L * |(n : ℝ)|))
      (2 / (Real.exp L - 1)) := by
  have he : Real.exp (-L) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_neg_of_pos hL)
  have h := hasSum_int_nonzero_natAbs_geometric (Real.exp (-L)) (Real.exp_pos _).le he
  simp_rw [← exp_int_abs_eq_natAbs_pow] at h
  convert h using 1
  rw [Real.exp_neg]
  have hne : Real.exp L ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp

/-- Absolute summability of all actual complex-density shifts. -/
theorem summable_norm_complexDensity_shifts (z : ℂ) (L : ℝ) (hL : 0 < L) :
    Summable (fun n : ℤ => ‖complexDensity (z + (L : ℂ) * (n : ℂ))‖) := by
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => complexDensity_shift_norm_le z L hL n)
    ((summable_int_exp_abs L hL).mul_left (densityAliasAmplitude z))

theorem summable_complexDensity_shifts (z : ℂ) (L : ℝ) (hL : 0 < L) :
    Summable (fun n : ℤ => complexDensity (z + (L : ℂ) * (n : ℂ))) :=
  (summable_norm_complexDensity_shifts z L hL).of_norm

theorem density_alias_norm_majorant_hasSum (z : ℂ) (L : ℝ) (hL : 0 < L) :
    HasSum (fun n : ℤ => if n = 0 then 0 else
      densityAliasAmplitude z * Real.exp (-L * |(n : ℝ)|))
      (2 * densityAliasAmplitude z / (Real.exp L - 1)) := by
  have h := (hasSum_int_nonzero_exp_abs L hL).mul_left (densityAliasAmplitude z)
  convert h using 1
  · funext n
    split_ifs <;> simp
  · ring

theorem summable_norm_nonzero_complexDensity_shifts (z : ℂ) (L : ℝ) (hL : 0 < L) :
    Summable (fun n : ℤ => if n = 0 then 0 else
      ‖complexDensity (z + (L : ℂ) * (n : ℂ))‖) := by
  apply Summable.of_nonneg_of_le _ _ (density_alias_norm_majorant_hasSum z L hL).summable
  · intro n
    split_ifs <;> positivity
  · intro n
    split_ifs
    · exact le_rfl
    · exact complexDensity_shift_norm_le z L hL n

/-- The sum of all nonzero alias norms is bounded by the exact two-sided
geometric sum. No alias is dropped through an assumed convergence premise. -/
theorem tsum_norm_nonzero_complexDensity_shifts_le (z : ℂ) (L : ℝ) (hL : 0 < L) :
    (∑' n : ℤ, if n = 0 then 0 else ‖complexDensity (z + (L : ℂ) * (n : ℂ))‖) ≤
      2 * densityAliasAmplitude z / (Real.exp L - 1) := by
  have hsum := summable_norm_nonzero_complexDensity_shifts z L hL
  have hb := density_alias_norm_majorant_hasSum z L hL
  rw [← hb.tsum_eq]
  apply hsum.tsum_le_tsum _ hb.summable
  intro n
  split_ifs
  · exact le_rfl
  · exact complexDensity_shift_norm_le z L hL n

theorem norm_tsum_nonzero_complexDensity_shifts_le (z : ℂ) (L : ℝ) (hL : 0 < L) :
    ‖∑' n : ℤ, if n = 0 then (0 : ℂ) else complexDensity (z + (L : ℂ) * (n : ℂ))‖ ≤
      2 * densityAliasAmplitude z / (Real.exp L - 1) := by
  have hnorm : Summable (fun n : ℤ => ‖if n = 0 then (0 : ℂ) else
      complexDensity (z + (L : ℂ) * (n : ℂ))‖) := by
    simpa only [apply_ite, norm_zero] using summable_norm_nonzero_complexDensity_shifts z L hL
  have h := (norm_tsum_le_tsum_norm hnorm).trans
    (by simpa only [apply_ite, norm_zero] using tsum_norm_nonzero_complexDensity_shifts_le z L hL)
  exact h

/-- Ready-to-compose alias error for the full lattice sum. -/
theorem complexDensity_lattice_error_le (z : ℂ) (L : ℝ) (hL : 0 < L) :
    ‖(∑' n : ℤ, complexDensity (z + (L : ℂ) * (n : ℂ))) - complexDensity z‖ ≤
      2 * densityAliasAmplitude z / (Real.exp L - 1) := by
  have he := (summable_complexDensity_shifts z L hL).tsum_eq_add_tsum_ite (0 : ℤ)
  simp only [Int.cast_zero, mul_zero, add_zero] at he
  rw [he, add_sub_cancel_left]
  exact norm_tsum_nonzero_complexDensity_shifts_le z L hL

/-- Actual infinite-trapezoid quadrature error, after the proved Poisson
identity. The right-hand side is analytic, not a supplied quadrature receipt. -/
theorem infiniteTrapezoid_error_le (z : ℂ) (h : ℝ) (hh : 0 < h) :
    ‖infiniteTrapezoid z h - complexDensity z‖ ≤
      2 * densityAliasAmplitude z / (Real.exp (2 * Real.pi / h) - 1) := by
  rw [infiniteTrapezoid_eq_tsum_complexDensity z h hh]
  exact complexDensity_lattice_error_le z (2 * Real.pi / h) (by positivity)

end ReciprocalXi
