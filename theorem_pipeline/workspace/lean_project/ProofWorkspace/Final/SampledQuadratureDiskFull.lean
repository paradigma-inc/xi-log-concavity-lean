import ProofWorkspace.Final.SampledQuadratureErrorFull

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

theorem reciprocal_cosine_norm_le_coarse (z : ℂ) (u : ℝ) (hi : |z.im| ≤ 1/4) :
    ‖reciprocalTransform u * Complex.cos (z*(u:ℂ))‖ ≤ 43046721 := by
  have hc := complex_cos_mul_real_norm_le z u (1/4) |u| hi le_rfl
  rw [norm_mul]
  by_cases hu : |u| ≤ 3
  · have he : Real.exp ((1/4)*|u|) ≤ 3 :=
      (Real.exp_le_exp.mpr (by linarith : (1/4:ℝ)*|u| ≤ 1)).trans Real.exp_one_lt_three.le
    have ht := mul_le_mul (reciprocalTransform_norm_le_two_central u hu) (hc.trans he)
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    norm_num at ht
    linarith
  · have hp := reciprocalTransform_norm_le_exp_of_abs_three_le u (1/4) (le_of_not_ge hu)
    have hb := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 16
    rw [← Real.exp_nat_mul] at hb
    norm_num at hb
    calc
      _ ≤ (reciprocalTailConstant (1/4) * Real.exp (-((1/4)*|u|))) *
          Real.exp ((1/4)*|u|) := mul_le_mul hp hc (norm_nonneg _)
            (mul_nonneg (reciprocalTailConstant_nonneg _) (Real.exp_pos _).le)
      _ = reciprocalTailConstant (1/4) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ Real.exp 16 := reciprocalTailConstant_quarter_le
      _ ≤ _ := hb

theorem sampledCosineQuadrature_large_strip_lt (z : ℂ) (v : ℕ → ℝ) (p : ℝ)
    (hi : |z.im| ≤ 1/4) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖sampledCosineQuadrature z (1/40) p 13600 v‖ < Real.exp 66 := by
  have he : (2/(10:ℝ)^120)*Real.exp 85 ≤ 1 := by
    have ht := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 85
    rw [← Real.exp_nat_mul] at ht
    norm_num only [Nat.cast_ofNat, mul_one] at ht
    calc
      _ ≤ (2/(10:ℝ)^120)*(3:ℝ)^85 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        norm_num at ht ⊢
        exact ht
      _ ≤ 1 := by norm_num
  have hvC : ∀ (k : ℕ), k ≤ 13600 →
      ‖reciprocalTransform ((k:ℝ)/40) - (v k:ℂ)‖ ≤ 2/(10:ℝ)^120 := by
    intro k hk
    rw [reciprocalTransform_sample_norm_eq_abs]
    exact hv k hk
  have ha : ∀ j ∈ Finset.range 13600,
      ‖(v (j+1):ℂ) * Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 43046722 := by
    intro j hj
    let u : ℝ := (1/40)*((j:ℝ)+1)
    have hu : |u| ≤ 340 := by
      have hjR : (j:ℝ)+1 ≤ 13600 := by exact_mod_cast (Finset.mem_range.mp hj)
      dsimp only [u]
      rw [abs_of_nonneg (by positivity)]
      linarith
    have hcos : ‖Complex.cos (z*(u:ℂ))‖ ≤ Real.exp 85 := by
      have ht := complex_cos_mul_real_norm_le z u (1/4) 340 hi hu
      norm_num at ht
      exact ht
    have hsample : ‖reciprocalTransform u - (v (j+1):ℂ)‖ ≤ 2/(10:ℝ)^120 := by
      have huEq : u = ((j+1:ℕ):ℝ)/40 := by dsimp [u]; push_cast; ring
      rw [huEq]
      exact hvC (j+1) (Finset.mem_range.mp hj)
    have hdiff : ‖(reciprocalTransform u - (v (j+1):ℂ))*Complex.cos (z*(u:ℂ))‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul hsample hcos (norm_nonneg _) (by positivity)).trans he
    have ht := norm_le_norm_sub_add ((v (j+1):ℂ)*Complex.cos (z*(u:ℂ)))
      (reciprocalTransform u*Complex.cos (z*(u:ℂ)))
    rw [norm_sub_rev, ← sub_mul] at ht
    have hb := reciprocal_cosine_norm_le_coarse z u hi
    change ‖(v (j+1):ℂ)*Complex.cos (z*(u:ℂ))‖ ≤ 43046722
    linarith
  have hsum : ‖∑ j ∈ Finset.range 13600,
      (v (j+1):ℂ)*Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 13600*(43046722:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range 13600, (43046722:ℝ) := Finset.sum_le_sum ha
      _ = _ := by simp
  have hv0 : |v 0| ≤ 2 := by
    have ht := hv 0 (by omega)
    simp only [Nat.cast_zero, zero_div, reciprocalTransform_zero, Complex.one_re] at ht
    have hδ : 2/(10:ℝ)^120 ≤ 1 := by norm_num
    rw [abs_le] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hz : ‖((v 0/2:ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    norm_num
    linarith
  have hn : ‖((v 0/2:ℝ):ℂ) + ∑ j ∈ Finset.range 13600,
      (v (j+1):ℂ)*Complex.cos (z*((1/40:ℝ)*((j:ℝ)+1):ℝ))‖ ≤ 1+13600*(43046722:ℝ) :=
    (norm_add_le _ _).trans (add_le_add hz hsum)
  have hp0 : 0 < p := by linarith
  have hnorm : (1/40:ℝ)/p ≤ 1/120 := by
    apply (div_le_iff₀ hp0).mpr
    linarith
  have h66 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) Real.exp_one_gt_two.le 66
  rw [← Real.exp_nat_mul] at h66
  norm_num only [Nat.cast_ofNat, mul_one] at h66
  unfold sampledCosineQuadrature
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (1/120:ℝ)*(1+13600*43046722) := mul_le_mul hnorm hn (norm_nonneg _) (by norm_num)
    _ < (2:ℝ)^66 := by norm_num
    _ ≤ _ := by norm_num at h66 ⊢; exact h66

def normalizedSampledQuadrature (c p : ℝ) (v : ℕ → ℝ) (z : ℂ) : ℂ :=
  sampledCosineQuadrature ((c:ℂ)+(1/200:ℂ)*z) (1/40) p 13600 v

theorem differentiable_normalizedSampledQuadrature (c p : ℝ) (v : ℕ → ℝ) :
    Differentiable ℂ (normalizedSampledQuadrature c p v) := by
  have hd := differentiable_sampledCosineQuadrature (1/40) p 13600 v
  unfold normalizedSampledQuadrature
  fun_prop

theorem normalizedSampledQuadrature_disk_lt (c p : ℝ) (v : ℕ → ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 50) (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖normalizedSampledQuadrature c p v z‖ < Real.exp 66 := by
  apply sampledCosineQuadrature_large_strip_lt _ v p _ hp hv
  have hIm : ((c:ℂ)+(1/200:ℂ)*z).im = (1/200:ℝ)*z.im := by norm_num [Complex.mul_im]
  rw [hIm, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/200)]
  have hi := (Complex.abs_im_le_norm z).trans hz
  linarith

def sampledTaylorCoefficient (c p : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℂ :=
  (n.factorial:ℂ)⁻¹ * iteratedDeriv n (normalizedSampledQuadrature c p v) 0

theorem sampledTaylorCoefficient_norm_le (c p : ℝ) (v : ℕ → ℝ) (n : ℕ)
    (hp : 3 ≤ p)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120) :
    ‖sampledTaylorCoefficient c p v n‖ ≤ Real.exp 66/(50:ℝ)^n := by
  have hF : ∀ w ∈ Metric.sphere (0:ℂ) 50,
      ‖normalizedSampledQuadrature c p v w‖ ≤ Real.exp 66 := by
    intro w hw
    have hn : ‖w‖ = 50 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    exact (normalizedSampledQuadrature_disk_lt c p v w hn.le hp hv).le
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<50) (differentiable_normalizedSampledQuadrature c p v).diffContOnCl hF
  have hn : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hm := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hn.le)
  unfold sampledTaylorCoefficient
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  convert hm using 1
  field_simp

theorem hasSum_sampledTaylor (c p : ℝ) (v : ℕ → ℝ) (z : ℂ) :
    HasSum (fun n : ℕ => sampledTaylorCoefficient c p v n * z^n)
      (normalizedSampledQuadrature c p v z) := by
  have ht := Complex.hasSum_taylorSeries_of_entire
    (differentiable_normalizedSampledQuadrature c p v) 0 z
  convert ht using 1
  funext n
  simp only [sampledTaylorCoefficient, smul_eq_mul, sub_zero]
  ring

end ReciprocalXi

