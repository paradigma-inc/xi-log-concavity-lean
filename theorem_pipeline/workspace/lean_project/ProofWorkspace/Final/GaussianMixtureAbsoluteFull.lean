import ProofWorkspace.Final.GaussianMixtureExponentialFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem exp_mul_abs_le_two_sided (q y : ℝ) :
    Real.exp (q*|y|)≤Real.exp (q*y)+Real.exp ((-q)*y) := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hy, mul_neg, neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem integrable_exp_abs_of_two_sided (ν : Measure ℝ) (q : ℝ)
    (hp : Integrable (fun y : ℝ ↦ Real.exp (q*y)) ν)
    (hn : Integrable (fun y : ℝ ↦ Real.exp ((-q)*y)) ν) :
    Integrable (fun y : ℝ ↦ Real.exp (q*|y|)) ν := by
  apply (hp.add hn).mono' (by fun_prop)
  filter_upwards with y
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply] using
    exp_mul_abs_le_two_sided q y

theorem integral_exp_abs_le_two_sided (ν : Measure ℝ) (q : ℝ)
    (hp : Integrable (fun y : ℝ ↦ Real.exp (q*y)) ν)
    (hn : Integrable (fun y : ℝ ↦ Real.exp ((-q)*y)) ν) :
    (∫ y : ℝ, Real.exp (q*|y|) ∂ν)≤exponentialMoment ν q+exponentialMoment ν (-q) := by
  have hh := integral_mono (integrable_exp_abs_of_two_sided ν q hp hn) (hp.add hn)
    (exp_mul_abs_le_two_sided q)
  simpa only [integral_add hp hn, exponentialMoment, Pi.add_apply] using hh

theorem gaussianVarianceMixture_even (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hn : ∀ᵐ s : ℝ ∂ν, 0≤s) :
    MeasurePreserving (fun y : ℝ ↦ -y) (gaussianVarianceMixture ν) (gaussianVarianceMixture ν) := by
  letI := gaussianVarianceMixture_isProbability ν
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_charFun
  ext u
  have hm := charFun_map_mul (μ:=gaussianVarianceMixture ν) (-1) u
  simp only [neg_one_mul] at hm
  rw [hm, charFun_gaussianVarianceMixture ν hn, charFun_gaussianVarianceMixture ν hn, neg_sq]

theorem gaussianVarianceMixture_absoluteMoment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hn : ∀ᵐ s : ℝ ∂ν, 0≤s) (q : ℝ)
    (hq : Integrable (fun s : ℝ ↦ Real.exp (q^2*s)) ν) :
    Integrable (fun y : ℝ ↦ Real.exp (q*|y|)) (gaussianVarianceMixture ν) ∧
      (∫ y : ℝ, Real.exp (q*|y|) ∂gaussianVarianceMixture ν)≤2*exponentialMoment ν (q^2) := by
  have hq' : Integrable (fun s : ℝ ↦ Real.exp ((-q)^2*s)) ν := by simpa only [neg_sq] using hq
  have hp := integrable_exp_gaussianVarianceMixture ν hn q hq
  have hm := integrable_exp_gaussianVarianceMixture ν hn (-q) hq'
  refine ⟨integrable_exp_abs_of_two_sided _ q hp hm, ?_⟩
  have hh := integral_exp_abs_le_two_sided _ q hp hm
  rw [exponentialMoment_gaussianVarianceMixture ν hn q hq,
    exponentialMoment_gaussianVarianceMixture ν hn (-q) hq', neg_sq] at hh
  linarith

end ReciprocalXi
