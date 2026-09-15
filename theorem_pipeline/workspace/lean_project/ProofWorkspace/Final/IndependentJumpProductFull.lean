import ProofWorkspace.Final.IndependentJumpSumFull
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem charFun_finiteJumpSum (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (N : ℕ) (u : ℝ) :
    charFun ((infinitePi ν).map (finiteJumpSum N)) u =
      ∏ n∈Finset.range N, charFun (ν n) u := by
  let phase (y : ℝ) : ℂ := Complex.exp ((u:ℂ)*(y:ℂ)*I)
  have hc : Continuous phase := by unfold phase; fun_prop
  have hind : iIndepFun (fun n : Fin N ↦ fun ω : ℕ → ℝ ↦ ω n) (infinitePi ν) := by
    exact (iIndepFun_infinitePi (P:=ν) (X:=fun _ ↦ (id : ℝ → ℝ))
      (fun _ ↦ measurable_id)).precomp Fin.val_injective
  have hprod := hind.integral_fun_prod_comp
    (fun n ↦ (measurable_pi_apply (n:ℕ)).aemeasurable)
    (f:=fun _ ↦ phase) (fun _ ↦ hc.aestronglyMeasurable)
  have hpoint (ω : ℕ → ℝ) : phase (finiteJumpSum N ω)=∏ n : Fin N, phase (ω n) := by
    rw [Fin.prod_univ_eq_prod_range (fun n ↦ phase (ω n)) N]
    simp only [phase, finiteJumpSum, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul,
      Complex.exp_sum]
  rw [charFun_apply_real, integral_map (measurable_finiteJumpSum N).aemeasurable
    hc.aestronglyMeasurable]
  change (∫ ω : ℕ → ℝ, phase (finiteJumpSum N ω) ∂infinitePi ν)=_
  simp_rw [hpoint]
  rw [hprod, Fin.prod_univ_eq_prod_range
    (fun n ↦ ∫ ω : ℕ → ℝ, phase (ω n) ∂infinitePi ν) N]
  apply Finset.prod_congr rfl
  intro n hn
  rw [← integral_map (measurable_pi_apply n).aemeasurable hc.aestronglyMeasurable,
    infinitePi_map_eval, charFun_apply_real]

theorem charFun_finiteCompoundPoissonSum (r : ℕ → ℝ≥0) (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (N : ℕ) (u : ℝ) :
    charFun ((infinitePi (fun n ↦ compoundPoissonLaw (r n) (ν n))).map
      (finiteJumpSum N)) u =
      Complex.exp (∑ n∈Finset.range N, (r n:ℂ)*(charFun (ν n) u-1)) := by
  rw [charFun_finiteJumpSum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro n hn
  exact charFun_compoundPoissonLaw (r n) (ν n) u

theorem charFun_independentJumpSum_eq_exp (ν : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] (hi : ∀ n, Integrable id (ν n))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂ν n))
    (g : ℕ → ℂ) (hg : Summable g) (u : ℝ)
    (he : ∀ n, charFun (ν n) u=Complex.exp (g n)) :
    charFun (independentJumpSumLaw ν) u=Complex.exp (∑' n, g n) := by
  have hp : ∀ N : ℕ, charFun ((infinitePi ν).map (finiteJumpSum N)) u=
      Complex.exp (∑ n∈Finset.range N, g n) := by
    intro N
    rw [charFun_finiteJumpSum, Complex.exp_sum]
    exact Finset.prod_congr rfl (fun n _ ↦ he n)
  have hh := tendsto_charFun_finiteJumpSum ν hi hs u
  simp_rw [hp] at hh
  exact tendsto_nhds_unique hh (Complex.continuous_exp.continuousAt.tendsto.comp
    hg.hasSum.tendsto_sum_nat)

end ReciprocalXi

