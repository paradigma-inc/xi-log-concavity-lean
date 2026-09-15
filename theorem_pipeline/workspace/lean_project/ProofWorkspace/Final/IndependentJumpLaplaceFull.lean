import ProofWorkspace.Final.NonnegativeLaplaceFull
import ProofWorkspace.Final.IndependentJumpProductFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem nonnegativeLaplace_finiteJumpSum (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (N : ℕ) (x : ℝ) :
    nonnegativeLaplace ((infinitePi ν).map (finiteJumpSum N)) x =
      ∏ n∈Finset.range N, nonnegativeLaplace (ν n) x := by
  let phase (y : ℝ) : ℝ := Real.exp (-x*y)
  have hc : Continuous phase := by unfold phase; fun_prop
  have hind : iIndepFun (fun n : Fin N ↦ fun ω : ℕ → ℝ ↦ ω n) (infinitePi ν) := by
    exact (iIndepFun_infinitePi (P:=ν) (X:=fun _ ↦ (id : ℝ → ℝ))
      (fun _ ↦ measurable_id)).precomp Fin.val_injective
  have hprod := hind.integral_fun_prod_comp
    (fun n ↦ (measurable_pi_apply (n:ℕ)).aemeasurable)
    (f:=fun _ ↦ phase) (fun _ ↦ hc.aestronglyMeasurable)
  have hpoint (ω : ℕ → ℝ) : phase (finiteJumpSum N ω)=∏ n : Fin N, phase (ω n) := by
    rw [Fin.prod_univ_eq_prod_range (fun n ↦ phase (ω n)) N]
    simp only [phase, finiteJumpSum, Finset.mul_sum, Real.exp_sum]
  rw [nonnegativeLaplace, integral_map (measurable_finiteJumpSum N).aemeasurable
    hc.aestronglyMeasurable]
  change (∫ ω : ℕ → ℝ, phase (finiteJumpSum N ω) ∂infinitePi ν)=_
  simp_rw [hpoint]
  rw [hprod, Fin.prod_univ_eq_prod_range
    (fun n ↦ ∫ ω : ℕ → ℝ, phase (ω n) ∂infinitePi ν) N]
  apply Finset.prod_congr rfl
  intro n hn
  rw [← integral_map (measurable_pi_apply n).aemeasurable hc.aestronglyMeasurable,
    infinitePi_map_eval]
  rfl

theorem tendsto_nonnegativeLaplace_finiteJumpSum (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂ν n, 0≤y) {x : ℝ} (hx : 0≤x) :
    Tendsto (fun N : ℕ ↦ nonnegativeLaplace ((infinitePi ν).map (finiteJumpSum N)) x)
      atTop (𝓝 (nonnegativeLaplace (independentJumpSumLaw ν) x)) := by
  let phase (y : ℝ) : ℝ := Real.exp (-x*y)
  have hc : Continuous phase := by unfold phase; fun_prop
  have hfinite (N : ℕ) : nonnegativeLaplace ((infinitePi ν).map (finiteJumpSum N)) x =
      ∫ ω : ℕ → ℝ, phase (finiteJumpSum N ω) ∂infinitePi ν := by
    rw [nonnegativeLaplace, integral_map (measurable_finiteJumpSum N).aemeasurable
      hc.aestronglyMeasurable]
  have hwhole : nonnegativeLaplace (independentJumpSumLaw ν) x=
      ∫ ω : ℕ → ℝ, phase (independentJumpSum ω) ∂infinitePi ν := by
    rw [independentJumpSumLaw, nonnegativeLaplace,
      integral_map (aemeasurable_independentJumpSum ν hi hs) hc.aestronglyMeasurable]
  have hall : ∀ᵐ ω : ℕ → ℝ ∂infinitePi ν, ∀ n, 0≤ω n := by
    apply ae_all_iff.mpr
    intro n
    exact (measurePreserving_eval_infinitePi ν n).quasiMeasurePreserving.ae (hn n)
  simp_rw [hfinite, hwhole]
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ))
  · intro N
    exact (hc.measurable.comp (measurable_finiteJumpSum N)).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    filter_upwards [hall] with ω hω
    have hy : 0≤finiteJumpSum N ω := Finset.sum_nonneg (fun n _ ↦ hω n)
    change ‖Real.exp (-x*finiteJumpSum N ω)‖≤1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hy)
  · filter_upwards [ae_summable_infinitePi_coordinates ν hi hs] with ω hω
    exact hc.continuousAt.tendsto.comp hω.of_norm.hasSum.tendsto_sum_nat

theorem nonnegativeLaplace_independentJumpSum_eq_exp (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂ν n, 0≤y)
    (g : ℕ → ℝ) (hg : Summable g) {x : ℝ} (hx : 0≤x)
    (he : ∀ n, nonnegativeLaplace (ν n) x=Real.exp (g n)) :
    nonnegativeLaplace (independentJumpSumLaw ν) x=Real.exp (∑' n, g n) := by
  have hp : ∀ N : ℕ, nonnegativeLaplace ((infinitePi ν).map (finiteJumpSum N)) x=
      Real.exp (∑ n∈Finset.range N, g n) := by
    intro N
    rw [nonnegativeLaplace_finiteJumpSum, Real.exp_sum]
    exact Finset.prod_congr rfl (fun n _ ↦ he n)
  have hh := tendsto_nonnegativeLaplace_finiteJumpSum ν hi hs hn hx
  simp_rw [hp] at hh
  exact tendsto_nhds_unique hh (Real.continuous_exp.continuousAt.tendsto.comp
    hg.hasSum.tendsto_sum_nat)

end ReciprocalXi

