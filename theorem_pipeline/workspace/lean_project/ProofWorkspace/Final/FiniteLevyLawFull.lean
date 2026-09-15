import ProofWorkspace.Final.CompoundPoissonMomentFull
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem finiteMeasure_eq_mass_smul_normalize (μ : FiniteMeasure ℝ) :
    (μ:Measure ℝ)=μ.mass • (μ.normalize:Measure ℝ) := by
  exact congrArg (fun η : FiniteMeasure ℝ ↦ (η:Measure ℝ)) μ.self_eq_mass_smul_normalize

def finiteLevyLaw (μ : FiniteMeasure ℝ) : Measure ℝ :=
  compoundPoissonLaw μ.mass (μ.normalize:Measure ℝ)

theorem finiteLevyLaw_isProbability (μ : FiniteMeasure ℝ) :
    IsProbabilityMeasure (finiteLevyLaw μ) :=
  inferInstanceAs (IsProbabilityMeasure (compoundPoissonLaw μ.mass (μ.normalize:Measure ℝ)))

theorem charFun_finiteLevyLaw (μ : FiniteMeasure ℝ) (u : ℝ) :
    charFun (finiteLevyLaw μ) u = Complex.exp
      (∫ y : ℝ, Complex.exp ((u:ℂ)*(y:ℂ)*I)-1 ∂(μ:Measure ℝ)) := by
  rw [finiteLevyLaw, charFun_compoundPoissonLaw]
  congr 1
  rw [finiteMeasure_eq_mass_smul_normalize μ, integral_smul_nnreal_measure]
  have hi : Integrable (fun y : ℝ ↦ Complex.exp ((u:ℂ)*(y:ℂ)*I))
      (μ.normalize:Measure ℝ) := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    filter_upwards with y
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [integral_sub hi (integrable_const 1), ← charFun_apply_real]
  simp [NNReal.smul_def, Complex.real_smul]

theorem integrable_id_normalize (μ : FiniteMeasure ℝ)
    (hi : Integrable id (μ:Measure ℝ)) : Integrable id (μ.normalize:Measure ℝ) := by
  by_cases h0 : μ=0
  · subst μ
    simp only [FiniteMeasure.normalize, show (0:FiniteMeasure ℝ).mass=0 from rfl]
    exact integrable_dirac (by exact enorm_lt_top)
  · rw [μ.toMeasure_normalize_eq_of_nonzero h0]
    exact hi.smul_measure_nnreal

theorem integrable_id_finiteLevyLaw (μ : FiniteMeasure ℝ)
    (hi : Integrable id (μ:Measure ℝ)) : Integrable id (finiteLevyLaw μ) :=
  integrable_id_compoundPoissonLaw μ.mass (μ.normalize:Measure ℝ)
    (integrable_id_normalize μ hi)

theorem lintegral_norm_finiteLevyLaw_le (μ : FiniteMeasure ℝ)
    (hi : Integrable id (μ:Measure ℝ)) :
    (∫⁻ y : ℝ, ‖y‖ₑ ∂finiteLevyLaw μ)≤ENNReal.ofReal (∫ y : ℝ, ‖y‖ ∂(μ:Measure ℝ)) := by
  have hh := lintegral_norm_compoundPoissonLaw_le μ.mass (μ.normalize:Measure ℝ)
    (integrable_id_normalize μ hi)
  have he : (∫ y : ℝ, ‖y‖ ∂(μ:Measure ℝ))=
      (μ.mass:ℝ)*(∫ y : ℝ, ‖y‖ ∂(μ.normalize:Measure ℝ)) := by
    rw [finiteMeasure_eq_mass_smul_normalize μ, integral_smul_nnreal_measure]
    rfl
  rw [he]
  exact hh

theorem finiteLevyLaw_zero : finiteLevyLaw 0=Measure.dirac 0 := by
  letI := finiteLevyLaw_isProbability 0
  apply Measure.ext_of_charFun
  ext u
  simp [charFun_finiteLevyLaw, charFun_dirac]

theorem ae_nonneg_finiteLevyLaw (μ : FiniteMeasure ℝ)
    (hn : ∀ᵐ y : ℝ ∂(μ:Measure ℝ), 0≤y) :
    ∀ᵐ y : ℝ ∂finiteLevyLaw μ, 0≤y := by
  by_cases h0 : μ=0
  · subst μ
    rw [finiteLevyLaw_zero]
    simp
  · apply ae_nonneg_compoundPoissonLaw
    rw [μ.toMeasure_normalize_eq_of_nonzero h0]
    exact ae_smul_measure hn _

end ReciprocalXi

