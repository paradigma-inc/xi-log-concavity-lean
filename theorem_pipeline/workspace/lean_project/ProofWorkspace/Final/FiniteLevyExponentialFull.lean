import ProofWorkspace.Final.CompoundPoissonExponentialFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem integrable_exp_normalize (μ : FiniteMeasure ℝ) (q : ℝ)
    (hi : Integrable (fun y : ℝ ↦ Real.exp (q*y)) (μ:Measure ℝ)) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (μ.normalize:Measure ℝ) := by
  by_cases h0 : μ=0
  · subst μ
    simp only [FiniteMeasure.normalize, show (0:FiniteMeasure ℝ).mass=0 from rfl]
    exact integrable_dirac (by exact enorm_lt_top)
  · rw [μ.toMeasure_normalize_eq_of_nonzero h0]
    exact hi.smul_measure_nnreal

theorem integrable_exp_finiteLevyLaw (μ : FiniteMeasure ℝ) (q : ℝ)
    (hi : Integrable (fun y : ℝ ↦ Real.exp (q*y)) (μ:Measure ℝ)) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (finiteLevyLaw μ) :=
  integrable_exp_compoundPoissonLaw μ.mass (μ.normalize:Measure ℝ) q
    (integrable_exp_normalize μ q hi)

theorem exponentialMoment_finiteLevyLaw (μ : FiniteMeasure ℝ) (q : ℝ)
    (hi : Integrable (fun y : ℝ ↦ Real.exp (q*y)) (μ:Measure ℝ)) :
    exponentialMoment (finiteLevyLaw μ) q=
      Real.exp (∫ y : ℝ, Real.exp (q*y)-1 ∂(μ:Measure ℝ)) := by
  rw [finiteLevyLaw, exponentialMoment_compoundPoissonLaw _ _ _
    (integrable_exp_normalize μ q hi)]
  congr 1
  rw [finiteMeasure_eq_mass_smul_normalize μ, integral_smul_nnreal_measure,
    integral_sub (integrable_exp_normalize μ q hi) (integrable_const 1)]
  simp [exponentialMoment, NNReal.smul_def, smul_eq_mul]

end ReciprocalXi
