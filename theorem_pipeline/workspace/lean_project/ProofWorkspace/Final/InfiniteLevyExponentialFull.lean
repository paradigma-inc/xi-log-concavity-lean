import ProofWorkspace.Final.FiniteLevyExponentialFull
import ProofWorkspace.Final.IndependentJumpExponentialFull
import ProofWorkspace.Final.InfiniteLevyLawFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem infiniteLevyLaw_exponentialMoment (μ : ℕ → FiniteMeasure ℝ)
    (hi : ∀ n, Integrable id (μ n:Measure ℝ))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂(μ n:Measure ℝ)))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂(μ n:Measure ℝ), 0≤y) {q : ℝ} (hq : 0≤q)
    (hk : Integrable (fun y : ℝ ↦ Real.exp (q*y)-1)
      (Measure.sum (fun n ↦ (μ n:Measure ℝ)))) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (infiniteLevyLaw μ) ∧
      exponentialMoment (infiniteLevyLaw μ) q=
        Real.exp (∫ y : ℝ, Real.exp (q*y)-1 ∂Measure.sum (fun n ↦ (μ n:Measure ℝ))) := by
  letI (n : ℕ) : IsProbabilityMeasure (finiteLevyLaw (μ n)) := finiteLevyLaw_isProbability (μ n)
  have hk' (n : ℕ) : Integrable (fun y : ℝ ↦ Real.exp (q*y)-1) (μ n:Measure ℝ) :=
    hk.mono_measure (Measure.le_sum _ n)
  have he' (n : ℕ) : Integrable (fun y : ℝ ↦ Real.exp (q*y)) (μ n:Measure ℝ) := by
    exact ((hk' n).add (integrable_const (1:ℝ))).congr
      (Eventually.of_forall (fun y ↦ sub_add_cancel (Real.exp (q*y)) 1))
  have hg := hasSum_integral_measure hk
  have hid := fun n ↦ integrable_id_finiteLevyLaw (μ n) (hi n)
  have hsum := summable_integral_norm_finiteLevyLaw μ hi hs
  have hnonneg := fun n ↦ ae_nonneg_finiteLevyLaw (μ n) (hn n)
  have hint := fun n ↦ integrable_exp_finiteLevyLaw (μ n) q (he' n)
  have hexact := fun n ↦ exponentialMoment_finiteLevyLaw (μ n) q (he' n)
  constructor
  · exact integrable_exp_independentJumpSumLaw _ hid hsum hnonneg hq hint _ hg.summable hexact
  · calc
      _ = Real.exp (∑' n : ℕ, ∫ y : ℝ, Real.exp (q*y)-1 ∂(μ n:Measure ℝ)) :=
        exponentialMoment_independentJumpSumLaw _ hid hsum hnonneg hq hint _ hg.summable hexact
      _ = _ := congrArg Real.exp hg.tsum_eq

theorem sfiniteLevyLaw_exponentialMoment (μ : Measure ℝ) [SFinite μ]
    (hi : Integrable id μ) (hn : ∀ᵐ y : ℝ ∂μ, 0≤y) {q : ℝ} (hq : 0≤q)
    (hk : Integrable (fun y : ℝ ↦ Real.exp (q*y)-1) μ) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (sfiniteLevyLaw μ) ∧
      exponentialMoment (sfiniteLevyLaw μ) q=
        Real.exp (∫ y : ℝ, Real.exp (q*y)-1 ∂μ) := by
  have hk' : Integrable (fun y : ℝ ↦ Real.exp (q*y)-1)
      (Measure.sum (fun n ↦ (sfiniteLevyPieces μ n:Measure ℝ))) := by
    change Integrable _ (Measure.sum (sfiniteSeq μ))
    rwa [sum_sfiniteSeq]
  have hh := infiniteLevyLaw_exponentialMoment (sfiniteLevyPieces μ)
    (integrable_id_sfiniteLevyPieces μ hi)
    (summable_integral_norm_sfiniteLevyPieces μ hi)
    (fun n ↦ ae_mono (sfiniteSeq_le μ n) hn) hq hk'
  change Integrable (fun y : ℝ ↦ Real.exp (q*y)) (sfiniteLevyLaw μ) ∧
    exponentialMoment (sfiniteLevyLaw μ) q=
      Real.exp (∫ y : ℝ, Real.exp (q*y)-1 ∂Measure.sum (sfiniteSeq μ)) at hh
  rwa [sum_sfiniteSeq] at hh

end ReciprocalXi
