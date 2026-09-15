import ProofWorkspace.Final.XiHeatTraceFull
import ProofWorkspace.Final.XiLogDerivativeFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace ReciprocalXi

theorem F_zeroHeatTerm_laplace_eq (z : FPositiveZeroOccurrence) (x t : ℝ) :
    Complex.exp (-(x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t =
      Complex.exp (-((F_pairRoot z)^2+(x:ℂ))*(t:ℂ)) := by
  rw [F_zeroHeatTerm, ← Complex.exp_add]
  congr 1
  ring

theorem integrableOn_F_zeroHeatTerm_laplace (z : FPositiveZeroOccurrence)
    {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp (-(x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t) (Ioi 0) := by
  simp_rw [F_zeroHeatTerm_laplace_eq]
  apply integrableOn_exp_mul_complex_Ioi
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
  linarith [F_pairRoot_sq_re_pos z]

theorem integral_norm_F_zeroHeatTerm_laplace (z : FPositiveZeroOccurrence)
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, ‖Complex.exp (-(x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t‖) =
      (((F_pairRoot z)^2).re+x)⁻¹ := by
  simp_rw [F_zeroHeatTerm_laplace_eq, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [integral_exp_mul_Ioi (by linarith [F_pairRoot_sq_re_pos z]) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

theorem integral_F_zeroHeatTerm_laplace (z : FPositiveZeroOccurrence)
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-(x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t) =
      ((F_pairRoot z)^2+(x:ℂ))⁻¹ := by
  simp_rw [F_zeroHeatTerm_laplace_eq]
  rw [integral_exp_mul_complex_Ioi (by
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith [F_pairRoot_sq_re_pos z]) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div]

theorem summable_integral_norm_F_zeroHeatTerm_laplace {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun z : FPositiveZeroOccurrence ↦
      ∫ t : ℝ in Ioi 0, ‖Complex.exp (-(x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t‖) := by
  simp_rw [integral_norm_F_zeroHeatTerm_laplace _ hx]
  apply summable_F_pairRoot_inv_sq_re.of_nonneg_of_le
  · intro z
    exact (inv_pos.mpr (add_pos_of_pos_of_nonneg (F_pairRoot_sq_re_pos z) hx)).le
  · intro z
    exact inv_anti₀ (F_pairRoot_sq_re_pos z) (le_add_of_nonneg_right hx)

theorem F_zeroHeatTrace_laplace_eq {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-(x:ℂ)*(t:ℂ))*F_zeroHeatTrace t) =
      ∑' z : FPositiveZeroOccurrence, ((F_pairRoot z)^2+(x:ℂ))⁻¹ := by
  letI : Countable FZero := F_zero_set_countable.to_subtype
  simp_rw [F_zeroHeatTrace, ← tsum_mul_left]
  rw [← integral_tsum_of_summable_integral_norm
    (fun z ↦ integrableOn_F_zeroHeatTerm_laplace z hx)
    (summable_integral_norm_F_zeroHeatTerm_laplace hx)]
  exact tsum_congr (fun z ↦ integral_F_zeroHeatTerm_laplace z hx)

theorem integrableOn_F_zeroHeatTrace_laplace {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp (-(x:ℂ)*(t:ℂ))*F_zeroHeatTrace t) (Ioi 0) := by
  apply integrableOn_F_zeroHeatTrace.bdd_mul (c:=1)
  · exact (show Continuous (fun t : ℝ ↦ Complex.exp (-(x:ℂ)*(t:ℂ))) by
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) ht.le

theorem reciprocalExtension_logDeriv_heat (u : ℝ) :
    logDeriv reciprocalExtension (u:ℂ) = -2*(u:ℂ)*
      ∫ t : ℝ in Ioi 0, Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))*F_zeroHeatTrace t := by
  rw [F_zeroHeatTrace_laplace_eq (sq_nonneg u)]
  have hden : DifferentiableAt ℂ (fun z : ℂ ↦ F (I*z)) (u:ℂ) :=
    (differentiable_F_complex.comp (differentiable_const I |>.mul differentiable_id)) _
  have hlin : HasDerivAt (fun z : ℂ ↦ I*z) I (u:ℂ) := by
    simpa using (hasDerivAt_id (u:ℂ)).const_mul I
  change logDeriv (fun z : ℂ ↦ F 0/F (I*z)) (u:ℂ) = _
  rw [logDeriv_div (f:=fun _ : ℂ ↦ F 0) (g:=fun z : ℂ ↦ F (I*z))
    (u:ℂ) F_zero_ne_zero (F_imaginary_axis_ne_zero u)
    (differentiableAt_const (F 0)) hden, logDeriv_const]
  simp only [Pi.zero_apply, zero_sub]
  change -logDeriv (F ∘ fun z : ℂ ↦ I*z) (u:ℂ) = _
  rw [logDeriv_comp (differentiable_F_complex _) hlin.differentiableAt, hlin.deriv,
    F_logDeriv_eq_paired_sum _ (F_imaginary_axis_ne_zero u),
    ← tsum_mul_right, ← tsum_neg, ← tsum_mul_left]
  apply tsum_congr
  intro z
  have he : (I*(u:ℂ))^2 = -(u:ℂ)^2 := by rw [mul_pow, Complex.I_sq]; ring
  rw [he, show -(u:ℂ)^2-(F_pairRoot z)^2 = -((F_pairRoot z)^2+(u:ℂ)^2) by ring,
    div_neg, Complex.ofReal_pow]
  rw [div_eq_mul_inv]
  linear_combination (2*(u:ℂ)*((F_pairRoot z)^2+(u:ℂ)^2)⁻¹) * Complex.I_mul_I

end ReciprocalXi

