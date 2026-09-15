import ProofWorkspace.Final.CompoundPoissonExponentialFull
import ProofWorkspace.Final.IndependentJumpLaplaceFull
import Mathlib.Probability.Moments.Basic

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem integrable_exp_finiteJumpSum (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (q : ℝ)
    (hq : ∀ n, Integrable (fun y : ℝ ↦ Real.exp (q*y)) (ν n)) (N : ℕ) :
    Integrable (fun ω : ℕ → ℝ ↦ Real.exp (q*finiteJumpSum N ω)) (infinitePi ν) := by
  have hind : iIndepFun (fun n : ℕ ↦ fun ω : ℕ → ℝ ↦ ω n) (infinitePi ν) :=
    iIndepFun_infinitePi (P:=ν) (X:=fun _ ↦ (id : ℝ → ℝ)) (fun _ ↦ measurable_id)
  have hc (n : ℕ) : Integrable (fun ω : ℕ → ℝ ↦ Real.exp (q*ω n)) (infinitePi ν) := by
    have hh : Integrable (fun y : ℝ ↦ Real.exp (q*y))
        ((infinitePi ν).map (fun ω : ℕ → ℝ ↦ ω n)) := by
      rw [infinitePi_map_eval]
      exact hq n
    exact hh.comp_aemeasurable (measurable_pi_apply n).aemeasurable
  simpa only [finiteJumpSum, Finset.sum_apply] using
    hind.integrable_exp_mul_sum (fun n ↦ measurable_pi_apply n)
      (s:=Finset.range N) (fun n _ ↦ hc n)

theorem exponentialMoment_finiteJumpSum (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (N : ℕ) (q : ℝ) :
    exponentialMoment ((infinitePi ν).map (finiteJumpSum N)) q=
      ∏ n∈Finset.range N, exponentialMoment (ν n) q := by
  simpa only [nonnegativeLaplace, neg_neg, exponentialMoment] using
    nonnegativeLaplace_finiteJumpSum ν N (-q)

theorem lintegral_exp_independentJumpSum (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂ν n, 0≤y) {q : ℝ} (hq0 : 0≤q)
    (hq : ∀ n, Integrable (fun y : ℝ ↦ Real.exp (q*y)) (ν n))
    (g : ℕ → ℝ) (hg : Summable g)
    (he : ∀ n, exponentialMoment (ν n) q=Real.exp (g n)) :
    (∫⁻ ω : ℕ → ℝ, ENNReal.ofReal (Real.exp (q*independentJumpSum ω)) ∂infinitePi ν)=
      ENNReal.ofReal (Real.exp (∑' n, g n)) := by
  have hall : ∀ᵐ ω : ℕ → ℝ ∂infinitePi ν, ∀ n, 0≤ω n := by
    apply ae_all_iff.mpr
    intro n
    exact (measurePreserving_eval_infinitePi ν n).quasiMeasurePreserving.ae (hn n)
  have hmono : ∀ᵐ ω : ℕ → ℝ ∂infinitePi ν,
      Monotone (fun N ↦ ENNReal.ofReal (Real.exp (q*finiteJumpSum N ω))) := by
    filter_upwards [hall] with ω hω
    apply monotone_nat_of_le_succ
    intro N
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hq0
    simp only [finiteJumpSum, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hω N)
  have ht : ∀ᵐ ω : ℕ → ℝ ∂infinitePi ν,
      Tendsto (fun N ↦ ENNReal.ofReal (Real.exp (q*finiteJumpSum N ω))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (q*independentJumpSum ω)))) := by
    filter_upwards [ae_summable_infinitePi_coordinates ν hi hs] with ω hω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul hω.of_norm.hasSum.tendsto_sum_nat))
  have hlimit := lintegral_tendsto_of_tendsto_of_monotone
    (fun N ↦ ((integrable_exp_finiteJumpSum ν q hq N).1.aemeasurable).ennreal_ofReal) hmono ht
  have hf (N : ℕ) :
      (∫⁻ ω : ℕ → ℝ, ENNReal.ofReal (Real.exp (q*finiteJumpSum N ω)) ∂infinitePi ν)=
        ENNReal.ofReal (Real.exp (∑ n∈Finset.range N, g n)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_finiteJumpSum ν q hq N)
      (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))]
    congr 1
    rw [← integral_map (measurable_finiteJumpSum N).aemeasurable
      (show AEStronglyMeasurable (fun y : ℝ ↦ Real.exp (q*y))
        ((infinitePi ν).map (finiteJumpSum N)) by fun_prop)]
    change exponentialMoment ((infinitePi ν).map (finiteJumpSum N)) q=_
    rw [exponentialMoment_finiteJumpSum, Real.exp_sum]
    exact Finset.prod_congr rfl (fun n _ ↦ he n)
  simp_rw [hf] at hlimit
  exact tendsto_nhds_unique hlimit (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_exp.continuousAt.tendsto.comp hg.hasSum.tendsto_sum_nat))

theorem integrable_exp_independentJumpSumLaw (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂ν n, 0≤y) {q : ℝ} (hq0 : 0≤q)
    (hq : ∀ n, Integrable (fun y : ℝ ↦ Real.exp (q*y)) (ν n))
    (g : ℕ → ℝ) (hg : Summable g)
    (he : ∀ n, exponentialMoment (ν n) q=Real.exp (g n)) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (independentJumpSumLaw ν) := by
  rw [independentJumpSumLaw, integrable_map_measure (by fun_prop)
    (aemeasurable_independentJumpSum ν hi hs)]
  refine ⟨(((aemeasurable_independentJumpSum ν hi hs).const_mul q).exp).aestronglyMeasurable, ?_⟩
  change (∫⁻ ω : ℕ → ℝ, ‖Real.exp (q*independentJumpSum ω)‖ₑ ∂infinitePi ν)<⊤
  simp_rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [lintegral_exp_independentJumpSum ν hi hs hn hq0 hq g hg he]
  exact ENNReal.ofReal_lt_top

theorem exponentialMoment_independentJumpSumLaw (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂ν n, 0≤y) {q : ℝ} (hq0 : 0≤q)
    (hq : ∀ n, Integrable (fun y : ℝ ↦ Real.exp (q*y)) (ν n))
    (g : ℕ → ℝ) (hg : Summable g)
    (he : ∀ n, exponentialMoment (ν n) q=Real.exp (g n)) :
    exponentialMoment (independentJumpSumLaw ν) q=Real.exp (∑' n, g n) := by
  have hIq := integrable_exp_independentJumpSumLaw ν hi hs hn hq0 hq g hg he
  have hI : Integrable (fun ω : ℕ → ℝ ↦ Real.exp (q*independentJumpSum ω)) (infinitePi ν) :=
    hIq.comp_aemeasurable (aemeasurable_independentJumpSum ν hi hs)
  have hh := lintegral_exp_independentJumpSum ν hi hs hn hq0 hq g hg he
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))] at hh
  rw [exponentialMoment, independentJumpSumLaw,
    integral_map (aemeasurable_independentJumpSum ν hi hs) (by fun_prop)]
  have hh' := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ (Real.exp_pos _).le)),
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh'

end ReciprocalXi
