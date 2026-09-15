import Mathlib.Probability.Distributions.Poisson
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory BoundedContinuousFunction
open scoped ENNReal NNReal
namespace ReciprocalXi

def convolutionPower (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n+1 => ν ∗ convolutionPower ν n

instance convolutionPower_isProbability (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (convolutionPower ν n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0:ℝ)))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsProbabilityMeasure (ν ∗ convolutionPower ν n))

theorem charFun_convolutionPower (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (u : ℝ) :
    charFun (convolutionPower ν n) u=(charFun ν u)^n := by
  induction n with
  | zero => simp [convolutionPower, charFun_dirac]
  | succ n ih =>
    rw [convolutionPower, charFun_conv, ih, pow_succ']

def compoundPoissonLaw (r : ℝ≥0) (ν : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ ↦ (poissonPMF r n) • convolutionPower ν n)

instance compoundPoissonLaw_isProbability (r : ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (compoundPoissonLaw r ν) := by
  constructor
  rw [compoundPoissonLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact (poissonPMF r).tsum_coe

theorem charFun_compoundPoissonLaw_series (r : ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (u : ℝ) : charFun (compoundPoissonLaw r ν) u =
      ∑' n : ℕ, (poissonPMFReal r n:ℂ)*(charFun ν u)^n := by
  rw [charFun_eq_integral_innerProbChar]
  have hi := BoundedContinuousFunction.integrable (compoundPoissonLaw r ν) (innerProbChar u)
  rw [compoundPoissonLaw, integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, ← charFun_eq_integral_innerProbChar, charFun_convolutionPower]
  change ((ENNReal.ofReal (poissonPMFReal r n)).toReal:ℂ)*(charFun ν u)^n = _
  rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg]

theorem hasSum_poisson_complex_powers (r : ℝ≥0) (z : ℂ) :
    HasSum (fun n : ℕ ↦ (poissonPMFReal r n:ℂ)*z^n)
      (Complex.exp ((r:ℂ)*(z-1))) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*z)).mul_left
    (Complex.exp (-(r:ℂ)))
  rw [← Complex.exp_eq_exp_ℂ] at hs
  convert hs using 1
  · ext n
    simp only [poissonPMFReal, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_natCast,
      mul_pow]
    ring
  · rw [← Complex.exp_add]
    congr 1
    ring

theorem charFun_compoundPoissonLaw (r : ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (u : ℝ) : charFun (compoundPoissonLaw r ν) u =
      Complex.exp ((r:ℂ)*(charFun ν u-1)) := by
  rw [charFun_compoundPoissonLaw_series]
  exact (hasSum_poisson_complex_powers r (charFun ν u)).tsum_eq

end ReciprocalXi
