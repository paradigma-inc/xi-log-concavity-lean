import ProofWorkspace.Final.InfiniteLevyLawFull
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

def heatLevyMeasure (H : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t ↦ ENNReal.ofReal (H t/t))

instance heatLevyMeasure_sfinite (H : ℝ → ℝ) : SFinite (heatLevyMeasure H) :=
  inferInstanceAs (SFinite ((volume.restrict (Ioi (0:ℝ))).withDensity
    (fun t ↦ ENNReal.ofReal (H t/t))))

theorem aemeasurable_heatLevyDensity {H : ℝ → ℝ} (hi : IntegrableOn H (Ioi 0)) :
    AEMeasurable (fun t : ℝ ↦ ENNReal.ofReal (H t/t)) (volume.restrict (Ioi 0)) :=
  (hi.1.aemeasurable.div measurable_id.aemeasurable).ennreal_ofReal

theorem integrable_id_heatLevyMeasure {H : ℝ → ℝ} (hi : IntegrableOn H (Ioi 0))
    (hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤H t) :
    Integrable id (heatLevyMeasure H) := by
  rw [heatLevyMeasure, integrable_withDensity_iff_integrable_smul₀'
    (aemeasurable_heatLevyDensity hi) (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply hi.congr
  filter_upwards [hn, ae_restrict_mem measurableSet_Ioi] with t hnt ht
  change 0<t at ht
  rw [ENNReal.toReal_ofReal (div_nonneg hnt ht.le), smul_eq_mul, id_eq,
    div_mul_cancel₀ _ ht.ne']

theorem ae_nonneg_heatLevyMeasure (H : ℝ → ℝ) :
    ∀ᵐ t : ℝ ∂heatLevyMeasure H, 0≤t := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact le_of_lt ht

theorem integral_heatLevyMeasure {H : ℝ → ℝ} (hi : IntegrableOn H (Ioi 0))
    (hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤H t) (g : ℝ → ℝ) :
    (∫ t : ℝ, g t ∂heatLevyMeasure H)=(∫ t : ℝ in Ioi 0, (H t/t)*g t) := by
  rw [heatLevyMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (aemeasurable_heatLevyDensity hi) (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hn, ae_restrict_mem measurableSet_Ioi] with t hnt ht
  rw [ENNReal.toReal_ofReal (div_nonneg hnt (le_of_lt ht)), smul_eq_mul]

def heatSubordinatorLaw (H : ℝ → ℝ) : Measure ℝ := sfiniteLevyLaw (heatLevyMeasure H)

theorem heatSubordinatorLaw_isProbability {H : ℝ → ℝ} (hi : IntegrableOn H (Ioi 0))
    (hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤H t) :
    IsProbabilityMeasure (heatSubordinatorLaw H) :=
  sfiniteLevyLaw_isProbability _ (integrable_id_heatLevyMeasure hi hn)

theorem ae_nonneg_heatSubordinatorLaw {H : ℝ → ℝ} (hi : IntegrableOn H (Ioi 0))
    (hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤H t) :
    ∀ᵐ t : ℝ ∂heatSubordinatorLaw H, 0≤t :=
  ae_nonneg_sfiniteLevyLaw _ (integrable_id_heatLevyMeasure hi hn) (ae_nonneg_heatLevyMeasure H)

theorem nonnegativeLaplace_heatSubordinatorLaw {H : ℝ → ℝ} (hi : IntegrableOn H (Ioi 0))
    (hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤H t) {x : ℝ} (hx : 0≤x) :
    nonnegativeLaplace (heatSubordinatorLaw H) x =
      Real.exp (∫ t : ℝ in Ioi 0, ((Real.exp (-x*t)-1)/t)*H t) := by
  rw [heatSubordinatorLaw, nonnegativeLaplace_sfiniteLevyLaw _
    (integrable_id_heatLevyMeasure hi hn) (ae_nonneg_heatLevyMeasure H) hx,
    integral_heatLevyMeasure hi hn]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  ring

end ReciprocalXi

