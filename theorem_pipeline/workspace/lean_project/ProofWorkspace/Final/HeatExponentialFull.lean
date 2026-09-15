import ProofWorkspace.Final.HeatSubordinatorFull
import ProofWorkspace.Final.InfiniteLevyExponentialFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem integrable_heatLevy_exponential_kernel {H : ℝ → ℝ} (hi : IntegrableOn H (Ioi 0))
    (hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤H t) (q : ℝ)
    (hk : IntegrableOn (fun t : ℝ ↦ ((Real.exp (q*t)-1)/t)*H t) (Ioi 0)) :
    Integrable (fun t : ℝ ↦ Real.exp (q*t)-1) (heatLevyMeasure H) := by
  rw [heatLevyMeasure, integrable_withDensity_iff_integrable_smul₀'
    (aemeasurable_heatLevyDensity hi) (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply hk.congr
  filter_upwards [hn, ae_restrict_mem measurableSet_Ioi] with t hnt ht
  rw [ENNReal.toReal_ofReal (div_nonneg hnt (le_of_lt ht)), smul_eq_mul]
  ring

theorem heatSubordinatorLaw_exponentialMoment {H : ℝ → ℝ} (hi : IntegrableOn H (Ioi 0))
    (hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤H t) {q : ℝ} (hq : 0≤q)
    (hk : IntegrableOn (fun t : ℝ ↦ ((Real.exp (q*t)-1)/t)*H t) (Ioi 0)) :
    Integrable (fun t : ℝ ↦ Real.exp (q*t)) (heatSubordinatorLaw H) ∧
      exponentialMoment (heatSubordinatorLaw H) q=
        Real.exp (∫ t : ℝ in Ioi 0, ((Real.exp (q*t)-1)/t)*H t) := by
  have hh := sfiniteLevyLaw_exponentialMoment (heatLevyMeasure H)
    (integrable_id_heatLevyMeasure hi hn) (ae_nonneg_heatLevyMeasure H) hq
    (integrable_heatLevy_exponential_kernel hi hn q hk)
  refine ⟨hh.1, hh.2.trans ?_⟩
  congr 1
  rw [integral_heatLevyMeasure hi hn]
  apply integral_congr_ae
  filter_upwards with t
  ring

end ReciprocalXi
