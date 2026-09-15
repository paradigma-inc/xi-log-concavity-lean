import ProofWorkspace.Final.XiHeatLaplaceFull
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory Metric
namespace ReciprocalXi

def F_heatExponentKernel (u t : ℝ) : ℂ := (((Real.exp (-u^2*t)-1)/t:ℝ):ℂ)

def F_heatExponentIntegrand (u t : ℝ) : ℂ := F_heatExponentKernel u t*F_zeroHeatTrace t

def F_heatExponent (u : ℝ) : ℂ := ∫ t : ℝ in Ioi 0, F_heatExponentIntegrand u t

def F_heatExponentDerivative (u t : ℝ) : ℂ :=
  -2*(u:ℂ)*Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))*F_zeroHeatTrace t

theorem norm_F_heatExponentKernel_le (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖F_heatExponentKernel u t‖ ≤ u^2 := by
  have hx : 0 ≤ u^2*t := mul_nonneg (sq_nonneg u) ht.le
  have he : Real.exp (-u^2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hl := Real.add_one_le_exp (-u^2*t)
  rw [F_heatExponentKernel, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonpos (sub_nonpos.mpr he), abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  nlinarith

theorem aestronglyMeasurable_F_heatExponentIntegrand (u : ℝ) :
    AEStronglyMeasurable (F_heatExponentIntegrand u) (volume.restrict (Ioi 0)) := by
  apply AEStronglyMeasurable.mul _ integrableOn_F_zeroHeatTrace.1
  exact (show Measurable (F_heatExponentKernel u) by
    unfold F_heatExponentKernel
    fun_prop).aestronglyMeasurable

theorem integrableOn_F_heatExponentIntegrand (u : ℝ) :
    IntegrableOn (F_heatExponentIntegrand u) (Ioi 0) := by
  apply (integrableOn_F_zeroHeatTrace.norm.const_mul (u^2)).mono'
    (aestronglyMeasurable_F_heatExponentIntegrand u)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [F_heatExponentIntegrand, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_F_heatExponentKernel_le u ht) (norm_nonneg _)

theorem F_heatExponentKernel_hasDerivAt (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun v : ℝ ↦ F_heatExponentKernel v t)
      (-2*(u:ℂ)*Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))) u := by
  have hd := (((((hasDerivAt_id u).pow 2).neg.mul_const t).exp.sub_const 1).div_const t)
  convert hd.ofReal_comp using 1
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat,
    mul_one, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, Complex.ofReal_pow, Complex.ofReal_exp]
  field_simp [ne_of_gt ht]

theorem F_heatExponentIntegrand_hasDerivAt (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun v : ℝ ↦ F_heatExponentIntegrand v t) (F_heatExponentDerivative u t) u :=
  (F_heatExponentKernel_hasDerivAt u ht).mul_const (F_zeroHeatTrace t)

theorem norm_F_heatExponentDerivative_le (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖F_heatExponentDerivative u t‖ ≤ 2 * |u| * ‖F_zeroHeatTrace t‖ := by
  have he : ‖Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u)) ht.le
  simp only [F_heatExponentDerivative, norm_mul, norm_neg, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 2 * |u| * 1 * ‖F_zeroHeatTrace t‖ := by gcongr
    _ = _ := by ring

theorem aestronglyMeasurable_F_heatExponentDerivative (u : ℝ) :
    AEStronglyMeasurable (F_heatExponentDerivative u) (volume.restrict (Ioi 0)) := by
  apply AEStronglyMeasurable.mul _ integrableOn_F_zeroHeatTrace.1
  exact (show Continuous (fun t : ℝ ↦ -2*(u:ℂ)*
    Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))) by fun_prop).aestronglyMeasurable

theorem F_heatExponent_hasDerivAt (u : ℝ) :
    HasDerivAt F_heatExponent
      (-2*(u:ℂ)*(∫ t : ℝ in Ioi 0,
        Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))*F_zeroHeatTrace t)) u := by
  have hb : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ v∈ball u 1,
      ‖F_heatExponentDerivative v t‖ ≤ 2*(|u|+1)*‖F_zeroHeatTrace t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro v hv
    have hv' : |v| ≤ |u|+1 := by
      have hd : |v-u| < 1 := by simpa [Real.dist_eq] using hv
      have hm := abs_add_le (v-u) u
      rw [sub_add_cancel] at hm
      linarith
    exact (norm_F_heatExponentDerivative_le v ht).trans (by gcongr)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F_heatExponentIntegrand) (F':=F_heatExponentDerivative)
    (μ:=volume.restrict (Ioi 0)) (x₀:=u) (s:=ball u 1)
    (bound:=fun t ↦ 2*(|u|+1)*‖F_zeroHeatTrace t‖)
    (ball_mem_nhds u (by norm_num))
    (Eventually.of_forall aestronglyMeasurable_F_heatExponentIntegrand)
    (integrableOn_F_heatExponentIntegrand u)
    (aestronglyMeasurable_F_heatExponentDerivative u) hb
    (integrableOn_F_zeroHeatTrace.norm.const_mul (2*(|u|+1)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact fun v _ ↦ F_heatExponentIntegrand_hasDerivAt v ht)
  convert hd.2 using 1
  simp only [F_heatExponentDerivative, mul_assoc, integral_const_mul]

theorem F_heatExponent_zero : F_heatExponent 0=0 := by
  simp [F_heatExponent, F_heatExponentIntegrand, F_heatExponentKernel]

theorem reciprocalTransform_hasDerivAt_heat (u : ℝ) :
    HasDerivAt reciprocalTransform
      ((-2*(u:ℂ)*(∫ t : ℝ in Ioi 0,
        Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))*F_zeroHeatTrace t))*reciprocalTransform u) u := by
  have hd := (differentiableAt_reciprocalExtension (u:ℂ) (by simp)).hasDerivAt.comp_ofReal
  have hn : reciprocalExtension (u:ℂ) ≠ 0 :=
    div_ne_zero F_zero_ne_zero (F_imaginary_axis_ne_zero u)
  have he := reciprocalExtension_logDeriv_heat u
  rw [logDeriv_apply] at he
  have hder := (div_eq_iff hn).mp he
  rw [reciprocalExtension_ofReal] at hder
  convert hd using 1
  exact hder.symm

/-- Actual exponential integral formula; the heat trace is not assumed positive. -/
theorem reciprocalTransform_eq_exp_heatExponent (u : ℝ) :
    reciprocalTransform u = Complex.exp (F_heatExponent u) := by
  let h (v : ℝ) := reciprocalTransform v*Complex.exp (-F_heatExponent v)
  have hh : ∀ v, HasDerivAt h 0 v := by
    intro v
    have hd := (reciprocalTransform_hasDerivAt_heat v).mul
      ((F_heatExponent_hasDerivAt v).neg.cexp)
    convert hd using 1
    ring
  have he := is_const_of_deriv_eq_zero (fun v ↦ (hh v).differentiableAt)
    (fun v ↦ (hh v).deriv) u 0
  have hzero : reciprocalTransform 0=1 := by simp [reciprocalTransform, F_zero_ne_zero]
  simp only [h, F_heatExponent_zero, neg_zero, Complex.exp_zero, mul_one, hzero] at he
  have hm := congrArg (fun z ↦ z*Complex.exp (F_heatExponent u)) he
  simpa only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    mul_one, one_mul] using hm

end ReciprocalXi
