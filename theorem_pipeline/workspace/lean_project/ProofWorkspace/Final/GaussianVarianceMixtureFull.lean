import ProofWorkspace.Final.InfiniteLevyLawFull
import Mathlib.Probability.Distributions.Gaussian.Real

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

def gaussianVarianceMixture (ν : Measure ℝ) : Measure ℝ :=
  (ν.prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ ↦ Real.sqrt (2*p.1)*p.2)

theorem gaussianVarianceMixture_isProbability (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (gaussianVarianceMixture ν) := by
  apply isProbabilityMeasure_map
  exact (show Measurable (fun p : ℝ × ℝ ↦ Real.sqrt (2*p.1)*p.2) by fun_prop).aemeasurable

theorem integral_gaussian_scaled_character {s : ℝ} (hs : 0≤s) (u : ℝ) :
    (∫ z : ℝ, Complex.exp ((u:ℂ)*((Real.sqrt (2*s)*z:ℝ):ℂ)*I) ∂gaussianReal 0 1)=
      (Real.exp (-u^2*s):ℂ) := by
  rw [← integral_map (show AEMeasurable (fun z : ℝ ↦ Real.sqrt (2*s)*z)
      (gaussianReal 0 1) by fun_prop)
    (show AEStronglyMeasurable (fun z : ℝ ↦ Complex.exp ((u:ℂ)*(z:ℂ)*I))
      ((gaussianReal 0 1).map (fun z : ℝ ↦ Real.sqrt (2*s)*z)) by fun_prop),
    ← charFun_apply_real, charFun_map_mul, charFun_gaussianReal]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  simp only [mul_zero, zero_mul, one_mul]
  have hh : ((Real.sqrt (2*s):ℂ))^2=(2:ℂ)*(s:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0≤2*s by positivity)
  rw [mul_pow, hh]
  ring

theorem charFun_gaussianVarianceMixture (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hn : ∀ᵐ s : ℝ ∂ν, 0≤s) (u : ℝ) :
    charFun (gaussianVarianceMixture ν) u=(nonnegativeLaplace ν (u^2):ℂ) := by
  have hi : Integrable (fun p : ℝ × ℝ ↦
      Complex.exp ((u:ℂ)*((Real.sqrt (2*p.1)*p.2:ℝ):ℂ)*I))
      (ν.prod (gaussianReal 0 1)) := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    filter_upwards with p
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [gaussianVarianceMixture, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop), integral_prod _ hi]
  calc
    _ = ∫ s : ℝ, (Real.exp (-(u^2)*s):ℂ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hn] with s hs
      exact integral_gaussian_scaled_character hs u
    _ = _ := by
      exact Complex.ofRealCLM.integral_comp_comm (integrable_nonnegativeLaplace ν hn (sq_nonneg u))

end ReciprocalXi

