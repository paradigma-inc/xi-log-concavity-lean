import ProofWorkspace.Final.CompoundPoissonMomentFull
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal
namespace ReciprocalXi

theorem integrable_infinitePi_coordinate (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n)) (n : ℕ) :
    Integrable (fun ω : ℕ → ℝ ↦ ω n) (infinitePi ν) := by
  have h : Integrable id ((infinitePi ν).map (fun ω : ℕ → ℝ ↦ ω n)) := by
    rw [infinitePi_map_eval]
    exact hi n
  exact h.comp_aemeasurable (measurable_pi_apply n).aemeasurable

theorem integral_norm_infinitePi_coordinate (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (n : ℕ) :
    (∫ ω : ℕ → ℝ, ‖ω n‖ ∂infinitePi ν)=(∫ y : ℝ, ‖y‖ ∂ν n) := by
  rw [← integral_map (measurable_pi_apply n).aemeasurable (by fun_prop), infinitePi_map_eval]

theorem ae_summable_infinitePi_coordinates (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n)) :
    ∀ᵐ ω : ℕ → ℝ ∂infinitePi ν, Summable (fun n ↦ ‖ω n‖) := by
  have hh : (∫⁻ ω : ℕ → ℝ, ∑' n : ℕ, ‖ω n‖ₑ ∂infinitePi ν)<⊤ := by
    rw [lintegral_tsum (fun n ↦ (integrable_infinitePi_coordinate ν hi n).1.enorm)]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_infinitePi_coordinate ν hi _),
      integral_norm_infinitePi_coordinate]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg (fun y ↦ norm_nonneg y)) hs]
    exact ENNReal.ofReal_lt_top
  have hm : Measurable (fun ω : ℕ → ℝ ↦ ∑' n : ℕ, ‖ω n‖ₑ) :=
    Measurable.ennreal_tsum (fun n ↦ (measurable_pi_apply n).enorm)
  filter_upwards [ae_lt_top hm hh.ne] with ω hω
  have hn : (∑' n : ℕ, (‖ω n‖₊:ℝ≥0∞))≠⊤ := by
    simpa only [enorm_eq_nnnorm] using hω.ne
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hn

def independentJumpSum (ω : ℕ → ℝ) : ℝ := ∑' n : ℕ, ω n

theorem aemeasurable_independentJumpSum (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n)) :
    AEMeasurable independentJumpSum (infinitePi ν) := by
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (f:=fun N : ℕ ↦ fun ω : ℕ → ℝ ↦ ∑ n∈Finset.range N, ω n)
  · intro N
    exact (show Measurable (fun ω : ℕ → ℝ ↦ ∑ n∈Finset.range N, ω n) by fun_prop).aemeasurable
  · filter_upwards [ae_summable_infinitePi_coordinates ν hi hs] with ω hω
    exact hω.of_norm.hasSum.tendsto_sum_nat

def independentJumpSumLaw (ν : ℕ → Measure ℝ) : Measure ℝ :=
  (infinitePi ν).map independentJumpSum

theorem independentJumpSumLaw_isProbability (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n)) :
    IsProbabilityMeasure (independentJumpSumLaw ν) :=
  isProbabilityMeasure_map (aemeasurable_independentJumpSum ν hi hs)

theorem ae_nonneg_independentJumpSumLaw (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂ν n, 0≤y) :
    ∀ᵐ y : ℝ ∂independentJumpSumLaw ν, 0≤y := by
  rw [independentJumpSumLaw, ae_map_iff (aemeasurable_independentJumpSum ν hi hs) measurableSet_Ici]
  have hall : ∀ᵐ ω : ℕ → ℝ ∂infinitePi ν, ∀ n, 0≤ω n := by
    apply ae_all_iff.mpr
    intro n
    exact (measurePreserving_eval_infinitePi ν n).quasiMeasurePreserving.ae (hn n)
  filter_upwards [hall] with ω hω
  exact tsum_nonneg hω

def finiteJumpSum (N : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ n∈Finset.range N, ω n

theorem measurable_finiteJumpSum (N : ℕ) : Measurable (finiteJumpSum N) := by
  unfold finiteJumpSum
  fun_prop

theorem tendsto_charFun_finiteJumpSum (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n)) (u : ℝ) :
    Tendsto (fun N : ℕ ↦ charFun ((infinitePi ν).map (finiteJumpSum N)) u) atTop
      (𝓝 (charFun (independentJumpSumLaw ν) u)) := by
  let phase (y : ℝ) : ℂ := Complex.exp ((u:ℂ)*(y:ℂ)*I)
  have hc : Continuous phase := by unfold phase; fun_prop
  have hfinite (N : ℕ) : charFun ((infinitePi ν).map (finiteJumpSum N)) u =
      ∫ ω : ℕ → ℝ, phase (finiteJumpSum N ω) ∂infinitePi ν := by
    rw [charFun_apply_real, integral_map (measurable_finiteJumpSum N).aemeasurable
      hc.aestronglyMeasurable]
  have hwhole : charFun (independentJumpSumLaw ν) u=
      ∫ ω : ℕ → ℝ, phase (independentJumpSum ω) ∂infinitePi ν := by
    rw [independentJumpSumLaw, charFun_apply_real,
      integral_map (aemeasurable_independentJumpSum ν hi hs) hc.aestronglyMeasurable]
  simp_rw [hfinite, hwhole]
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ))
  · intro N
    exact (hc.measurable.comp (measurable_finiteJumpSum N)).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    filter_upwards with ω
    simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  · filter_upwards [ae_summable_infinitePi_coordinates ν hi hs] with ω hω
    exact hc.continuousAt.tendsto.comp hω.of_norm.hasSum.tendsto_sum_nat

end ReciprocalXi

