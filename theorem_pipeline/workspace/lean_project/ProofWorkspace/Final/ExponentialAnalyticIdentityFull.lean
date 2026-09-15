import ProofWorkspace.Final.GaussianMixtureAbsoluteFull
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem integrable_exp_of_absoluteMoment (μ : Measure ℝ) {R : ℝ}
    (hM : Integrable (fun y : ℝ ↦ Real.exp (R*|y|)) μ) {q : ℝ} (hq : |q|≤R) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) μ := by
  apply hM.mono' (by fun_prop)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    q*y≤|q*y| := le_abs_self _
    _ = |q| * |y| := abs_mul _ _
    _ ≤ R*|y| := mul_le_mul_of_nonneg_right hq (abs_nonneg y)

theorem interior_integrableExpSet_of_absoluteMoment (μ : Measure ℝ) {R : ℝ}
    (hM : Integrable (fun y : ℝ ↦ Real.exp (R*|y|)) μ) :
    Ioo (-R) R ⊆ interior (integrableExpSet id μ) := by
  have hsub : Ioo (-R) R ⊆ integrableExpSet id μ := by
    intro q hq
    exact integrable_exp_of_absoluteMoment μ hM
      (abs_le.mpr ⟨hq.1.le, hq.2.le⟩)
  simpa only [isOpen_Ioo.interior_eq] using interior_mono hsub

theorem complexMGF_identity_from_imaginary (μ : Measure ℝ) {R : ℝ} (hR : 0<R)
    (hM : Integrable (fun y : ℝ ↦ Real.exp (R*|y|)) μ)
    (A B : ℂ → ℂ) (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (haxis : ∀ u : ℝ, complexMGF id μ ((u:ℂ)*I)*A ((u:ℂ)*I)=B ((u:ℂ)*I))
    {w : ℂ} (hw : |w.re|<R) :
    complexMGF id μ w*A w=B w := by
  let U : Set ℂ := {z | z.re∈Ioo (-R) R}
  have hU : IsPreconnected U :=
    ((convex_Ioo (-R) R).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hAo : AnalyticOnNhd ℂ A U := by
    intro z hz
    exact hA.analyticAt z
  have hBo : AnalyticOnNhd ℂ B U := by
    intro z hz
    exact hB.analyticAt z
  have hMo : AnalyticOnNhd ℂ (complexMGF id μ) U := by
    intro z hz
    exact analyticAt_complexMGF (interior_integrableExpSet_of_absoluteMoment μ hM hz)
  have hlim : Tendsto (fun n : ℕ ↦ ((1/((n:ℝ)+1):ℝ):ℂ)*I) atTop (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
      simpa only [Complex.ofReal_zero, zero_mul] using hr.mul_const I
    · filter_upwards with n
      simp only [mem_compl_iff, mem_singleton_iff]
      apply mul_ne_zero _ I_ne_zero
      exact_mod_cast (show (1/((n:ℝ)+1):ℝ)≠0 by positivity)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), complexMGF id μ z*A z=B z :=
    hlim.frequently ((Eventually.of_forall (fun n : ℕ ↦ haxis (1/((n:ℝ)+1)))).frequently)
  exact (hMo.mul hAo).eqOn_of_preconnected_of_frequently_eq hBo hU
    (by simp only [U, mem_setOf_eq, Complex.zero_re, mem_Ioo]; constructor <;> linarith)
    hfreq (abs_lt.mp hw)

end ReciprocalXi
