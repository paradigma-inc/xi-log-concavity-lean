import ProofWorkspace.Final.AngularFourierInversionFull
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
namespace ReciprocalXi

theorem integrable_angular_character_product (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℂ) (hf : Integrable f) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ f p.1*Complex.exp ((p.1:ℂ)*(p.2:ℂ)*I)*
      Complex.exp (-I*(x:ℂ)*(p.1:ℂ))) (volume.prod μ) := by
  apply (hf.norm.mul_prod (integrable_const (1:ℝ))).mono'
  · apply AEStronglyMeasurable.mul _ (by fun_prop)
    exact hf.1.comp_fst.mul (by fun_prop)
  · filter_upwards with p
    simp [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem angularInverse_mul_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℂ) (hf : Integrable f) (x : ℝ) :
    angularInverse (fun u : ℝ ↦ f u*charFun μ u) x=
      ∫ y : ℝ, angularInverse f (x-y) ∂μ := by
  have hi := integrable_angular_character_product μ f hf x
  have hu (u : ℝ) : f u*charFun μ u*Complex.exp (-I*(x:ℂ)*(u:ℂ))=
      ∫ y : ℝ, f u*Complex.exp ((u:ℂ)*(y:ℂ)*I)*Complex.exp (-I*(x:ℂ)*(u:ℂ)) ∂μ := by
    rw [charFun_apply_real, integral_mul_const, integral_const_mul]
  have hp (u y : ℝ) : f u*Complex.exp ((u:ℂ)*(y:ℂ)*I)*Complex.exp (-I*(x:ℂ)*(u:ℂ))=
      f u*Complex.exp (-I*((x-y:ℝ):ℂ)*(u:ℂ)) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [angularInverse]
  simp_rw [hu]
  rw [integral_integral_swap hi]
  simp_rw [hp]
  rw [← integral_div]
  rfl

end ReciprocalXi
