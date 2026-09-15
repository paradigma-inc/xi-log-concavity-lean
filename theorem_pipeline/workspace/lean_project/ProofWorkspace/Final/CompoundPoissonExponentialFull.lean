import ProofWorkspace.Final.NonnegativeLaplaceFull
import ProofWorkspace.Final.ConvolutionRemainderFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem integrable_exp_convolutionPower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (q : ℝ) (hq : Integrable (fun y : ℝ ↦ Real.exp (q*y)) ν) (n : ℕ) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (convolutionPower ν n) := by
  induction n with
  | zero => exact integrable_dirac (by simp)
  | succ n ih =>
    rw [convolutionPower, Measure.conv, integrable_map_measure (by fun_prop) (by fun_prop)]
    convert hq.mul_prod ih using 1
    ext p
    simp [Function.comp_def, mul_add, Real.exp_add]

theorem exponentialMoment_convolutionPower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (q : ℝ) (hq : Integrable (fun y : ℝ ↦ Real.exp (q*y)) ν) (n : ℕ) :
    exponentialMoment (convolutionPower ν n) q=(exponentialMoment ν q)^n := by
  induction n with
  | zero => simp [exponentialMoment, convolutionPower]
  | succ n ih =>
    have hi := integrable_exp_convolutionPower ν q hq (n+1)
    rw [convolutionPower] at hi
    rw [exponentialMoment, convolutionPower, integral_conv hi]
    simp_rw [mul_add, Real.exp_add, integral_const_mul]
    rw [integral_mul_const]
    change exponentialMoment ν q*exponentialMoment (convolutionPower ν n) q=_
    rw [ih, pow_succ']

theorem integrable_exp_compoundPoissonLaw (r : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (q : ℝ) (hq : Integrable (fun y : ℝ ↦ Real.exp (q*y)) ν) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (compoundPoissonLaw r ν) := by
  refine ⟨by fun_prop, ?_⟩
  have hM : 0≤exponentialMoment ν q := integral_nonneg (fun _ ↦ (Real.exp_pos _).le)
  have hm (n : ℕ) : (∫ y : ℝ, ‖Real.exp (q*y)‖ ∂convolutionPower ν n)=
      (exponentialMoment ν q)^n := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), exponentialMoment] using
      exponentialMoment_convolutionPower ν q hq n
  change (∫⁻ y : ℝ, ‖Real.exp (q*y)‖ₑ ∂compoundPoissonLaw r ν)<⊤
  rw [compoundPoissonLaw, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul,
    ← ofReal_integral_norm_eq_lintegral_enorm (integrable_exp_convolutionPower ν q hq _), hm]
  have he (n : ℕ) : (poissonPMF r n)*ENNReal.ofReal ((exponentialMoment ν q)^n)=
      ENNReal.ofReal (poissonPMFReal r n*(exponentialMoment ν q)^n) := by
    change ENNReal.ofReal (poissonPMFReal r n)*ENNReal.ofReal _=_
    exact (ENNReal.ofReal_mul poissonPMFReal_nonneg).symm
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n ↦ mul_nonneg poissonPMFReal_nonneg (pow_nonneg hM n))
    (hasSum_poisson_real_powers r (exponentialMoment ν q)).summable]
  exact ENNReal.ofReal_lt_top

theorem exponentialMoment_compoundPoissonLaw (r : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (q : ℝ) (hq : Integrable (fun y : ℝ ↦ Real.exp (q*y)) ν) :
    exponentialMoment (compoundPoissonLaw r ν) q=
      Real.exp ((r:ℝ)*(exponentialMoment ν q-1)) := by
  have hi := integrable_exp_compoundPoissonLaw r ν q hq
  rw [exponentialMoment, compoundPoissonLaw, integral_sum_measure hi]
  have he (n : ℕ) : (∫ y : ℝ, Real.exp (q*y) ∂(poissonPMF r n) • convolutionPower ν n)=
      poissonPMFReal r n*(exponentialMoment ν q)^n := by
    rw [integral_smul_measure]
    change (ENNReal.ofReal (poissonPMFReal r n)).toReal*exponentialMoment (convolutionPower ν n) q=_
    rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, exponentialMoment_convolutionPower ν q hq n]
  simp_rw [he]
  exact (hasSum_poisson_real_powers r (exponentialMoment ν q)).tsum_eq

end ReciprocalXi
