import ProofWorkspace.Final.GaussianVarianceMixtureFull
import ProofWorkspace.Final.CompoundPoissonExponentialFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem integrable_gaussian_scaled_exponential (s q : ℝ) :
    Integrable (fun z : ℝ ↦ Real.exp (q*(Real.sqrt (2*s)*z))) (gaussianReal 0 1) := by
  simpa only [mul_assoc] using
    (integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (q*Real.sqrt (2*s)))

theorem integral_gaussian_scaled_exponential {s : ℝ} (hs : 0≤s) (q : ℝ) :
    (∫ z : ℝ, Real.exp (q*(Real.sqrt (2*s)*z)) ∂gaussianReal 0 1)=
      Real.exp (q^2*s) := by
  have hh := congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1)) (q*Real.sqrt (2*s))
  simp only [mgf, mul_assoc] at hh
  rw [hh]
  congr 1
  rw [mul_pow, Real.sq_sqrt (show 0≤2*s by positivity)]
  norm_num
  ring

theorem integrable_exp_gaussianVarianceMixture (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hn : ∀ᵐ s : ℝ ∂ν, 0≤s) (q : ℝ)
    (hq : Integrable (fun s : ℝ ↦ Real.exp (q^2*s)) ν) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (gaussianVarianceMixture ν) := by
  rw [gaussianVarianceMixture, integrable_map_measure (by fun_prop) (by fun_prop)]
  apply (integrable_prod_iff (by fun_prop)).mpr
  constructor
  · exact Eventually.of_forall (fun s ↦ integrable_gaussian_scaled_exponential s q)
  · apply hq.congr
    filter_upwards [hn] with s hs
    simp only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (integral_gaussian_scaled_exponential hs q).symm

theorem exponentialMoment_gaussianVarianceMixture (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hn : ∀ᵐ s : ℝ ∂ν, 0≤s) (q : ℝ)
    (hq : Integrable (fun s : ℝ ↦ Real.exp (q^2*s)) ν) :
    exponentialMoment (gaussianVarianceMixture ν) q=exponentialMoment ν (q^2) := by
  have hi := integrable_exp_gaussianVarianceMixture ν hn q hq
  rw [gaussianVarianceMixture, integrable_map_measure (by fun_prop) (by fun_prop)] at hi
  change Integrable (fun p : ℝ × ℝ ↦ Real.exp (q*(Real.sqrt (2*p.1)*p.2)))
    (ν.prod (gaussianReal 0 1)) at hi
  rw [exponentialMoment, gaussianVarianceMixture,
    integral_map (by fun_prop) (by fun_prop), integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hn] with s hs
  exact integral_gaussian_scaled_exponential hs q

end ReciprocalXi
