import ProofWorkspace.Final.IndependentJumpLaplaceFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem norm_laplace_sub_one_le {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    ‖Real.exp (-x*y)-1‖≤x*‖y‖ := by
  have he : Real.exp (-x*y)≤1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hy)
  have hl := Real.add_one_le_exp (-x*y)
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr he), Real.norm_eq_abs, abs_of_nonneg hy]
  linarith

theorem integrable_laplace_sub_one (μ : Measure ℝ) (hi : Integrable id μ)
    (hn : ∀ᵐ y : ℝ ∂μ, 0≤y) {x : ℝ} (hx : 0≤x) :
    Integrable (fun y : ℝ ↦ Real.exp (-x*y)-1) μ := by
  apply (hi.norm.const_mul x).mono' (by fun_prop)
  filter_upwards [hn] with y hy
  exact norm_laplace_sub_one_le hx hy

theorem integrable_id_sum_finiteMeasure (μ : ℕ → FiniteMeasure ℝ)
    (hi : ∀ n, Integrable id (μ n:Measure ℝ))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂(μ n:Measure ℝ))) :
    Integrable id (Measure.sum (fun n ↦ (μ n:Measure ℝ))) := by
  refine ⟨by fun_prop, ?_⟩
  change (∫⁻ y : ℝ, ‖y‖ₑ ∂Measure.sum (fun n ↦ (μ n:Measure ℝ)))<⊤
  rw [lintegral_sum_measure]
  have hi' (n : ℕ) : Integrable (fun y : ℝ ↦ y) (μ n:Measure ℝ) := hi n
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi' _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg (fun y ↦ norm_nonneg y)) hs]
  exact ENNReal.ofReal_lt_top

theorem integral_norm_finiteLevyLaw_le (μ : FiniteMeasure ℝ)
    (hi : Integrable id (μ:Measure ℝ)) :
    (∫ y : ℝ, ‖y‖ ∂finiteLevyLaw μ)≤∫ y : ℝ, ‖y‖ ∂(μ:Measure ℝ) := by
  have hh := lintegral_norm_finiteLevyLaw_le μ hi
  have hi' : Integrable (fun y : ℝ ↦ y) (finiteLevyLaw μ) := integrable_id_finiteLevyLaw μ hi
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi'] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun y ↦ norm_nonneg y))).mp hh

theorem summable_integral_norm_finiteLevyLaw (μ : ℕ → FiniteMeasure ℝ)
    (hi : ∀ n, Integrable id (μ n:Measure ℝ))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂(μ n:Measure ℝ))) :
    Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂finiteLevyLaw (μ n)) := by
  exact Summable.of_nonneg_of_le (fun n ↦ integral_nonneg (fun y ↦ norm_nonneg y))
    (fun n ↦ integral_norm_finiteLevyLaw_le (μ n) (hi n)) hs

def infiniteLevyLaw (μ : ℕ → FiniteMeasure ℝ) : Measure ℝ :=
  independentJumpSumLaw (fun n ↦ finiteLevyLaw (μ n))

theorem infiniteLevyLaw_isProbability (μ : ℕ → FiniteMeasure ℝ)
    (hi : ∀ n, Integrable id (μ n:Measure ℝ))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂(μ n:Measure ℝ))) :
    IsProbabilityMeasure (infiniteLevyLaw μ) := by
  letI (n : ℕ) : IsProbabilityMeasure (finiteLevyLaw (μ n)) := finiteLevyLaw_isProbability (μ n)
  exact independentJumpSumLaw_isProbability _
    (fun n ↦ integrable_id_finiteLevyLaw (μ n) (hi n)) (summable_integral_norm_finiteLevyLaw μ hi hs)

theorem ae_nonneg_infiniteLevyLaw (μ : ℕ → FiniteMeasure ℝ)
    (hi : ∀ n, Integrable id (μ n:Measure ℝ))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂(μ n:Measure ℝ)))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂(μ n:Measure ℝ), 0≤y) :
    ∀ᵐ y : ℝ ∂infiniteLevyLaw μ, 0≤y := by
  letI (n : ℕ) : IsProbabilityMeasure (finiteLevyLaw (μ n)) := finiteLevyLaw_isProbability (μ n)
  exact ae_nonneg_independentJumpSumLaw _
    (fun n ↦ integrable_id_finiteLevyLaw (μ n) (hi n))
    (summable_integral_norm_finiteLevyLaw μ hi hs) (fun n ↦ ae_nonneg_finiteLevyLaw (μ n) (hn n))

theorem nonnegativeLaplace_infiniteLevyLaw (μ : ℕ → FiniteMeasure ℝ)
    (hi : ∀ n, Integrable id (μ n:Measure ℝ))
    (hs : Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂(μ n:Measure ℝ)))
    (hn : ∀ n, ∀ᵐ y : ℝ ∂(μ n:Measure ℝ), 0≤y) {x : ℝ} (hx : 0≤x) :
    nonnegativeLaplace (infiniteLevyLaw μ) x = Real.exp
      (∫ y : ℝ, Real.exp (-x*y)-1 ∂Measure.sum (fun n ↦ (μ n:Measure ℝ))) := by
  letI (n : ℕ) : IsProbabilityMeasure (finiteLevyLaw (μ n)) := finiteLevyLaw_isProbability (μ n)
  have ha : ∀ᵐ y : ℝ ∂Measure.sum (fun n ↦ (μ n:Measure ℝ)), 0≤y := ae_sum_iff.mpr hn
  have hk := integrable_laplace_sub_one _ (integrable_id_sum_finiteMeasure μ hi hs) ha hx
  have hg := hasSum_integral_measure hk
  calc
    _ = Real.exp (∑' n : ℕ, ∫ y : ℝ, Real.exp (-x*y)-1 ∂(μ n:Measure ℝ)) := by
      exact nonnegativeLaplace_independentJumpSum_eq_exp _
        (fun n ↦ integrable_id_finiteLevyLaw (μ n) (hi n))
        (summable_integral_norm_finiteLevyLaw μ hi hs)
        (fun n ↦ ae_nonneg_finiteLevyLaw (μ n) (hn n)) _ hg.summable hx
        (fun n ↦ nonnegativeLaplace_finiteLevyLaw (μ n) (hn n) hx)
    _ = _ := congrArg Real.exp hg.tsum_eq

def sfiniteLevyPieces (μ : Measure ℝ) [SFinite μ] (n : ℕ) : FiniteMeasure ℝ :=
  ⟨sfiniteSeq μ n, inferInstance⟩

theorem integrable_id_sfiniteLevyPieces (μ : Measure ℝ) [SFinite μ]
    (hi : Integrable id μ) (n : ℕ) : Integrable id (sfiniteLevyPieces μ n:Measure ℝ) :=
  hi.mono_measure (sfiniteSeq_le μ n)

theorem summable_integral_norm_sfiniteLevyPieces (μ : Measure ℝ) [SFinite μ]
    (hi : Integrable id μ) :
    Summable (fun n ↦ ∫ y : ℝ, ‖y‖ ∂(sfiniteLevyPieces μ n:Measure ℝ)) := by
  have hh : Integrable (fun y : ℝ ↦ ‖y‖) (Measure.sum (sfiniteSeq μ)) := by
    rw [sum_sfiniteSeq]
    exact hi.norm
  exact (hasSum_integral_measure hh).summable

def sfiniteLevyLaw (μ : Measure ℝ) [SFinite μ] : Measure ℝ :=
  infiniteLevyLaw (sfiniteLevyPieces μ)

theorem sfiniteLevyLaw_isProbability (μ : Measure ℝ) [SFinite μ]
    (hi : Integrable id μ) : IsProbabilityMeasure (sfiniteLevyLaw μ) :=
  infiniteLevyLaw_isProbability _ (integrable_id_sfiniteLevyPieces μ hi)
    (summable_integral_norm_sfiniteLevyPieces μ hi)

theorem ae_nonneg_sfiniteLevyLaw (μ : Measure ℝ) [SFinite μ]
    (hi : Integrable id μ) (hn : ∀ᵐ y : ℝ ∂μ, 0≤y) :
    ∀ᵐ y : ℝ ∂sfiniteLevyLaw μ, 0≤y := by
  apply ae_nonneg_infiniteLevyLaw _ (integrable_id_sfiniteLevyPieces μ hi)
    (summable_integral_norm_sfiniteLevyPieces μ hi)
  intro n
  exact ae_mono (sfiniteSeq_le μ n) hn

theorem nonnegativeLaplace_sfiniteLevyLaw (μ : Measure ℝ) [SFinite μ]
    (hi : Integrable id μ) (hn : ∀ᵐ y : ℝ ∂μ, 0≤y) {x : ℝ} (hx : 0≤x) :
    nonnegativeLaplace (sfiniteLevyLaw μ) x =
      Real.exp (∫ y : ℝ, Real.exp (-x*y)-1 ∂μ) := by
  have hh := nonnegativeLaplace_infiniteLevyLaw (sfiniteLevyPieces μ)
    (integrable_id_sfiniteLevyPieces μ hi)
    (summable_integral_norm_sfiniteLevyPieces μ hi)
    (fun n ↦ ae_mono (sfiniteSeq_le μ n) hn) hx
  change nonnegativeLaplace (sfiniteLevyLaw μ) x=
    Real.exp (∫ y : ℝ, Real.exp (-x*y)-1 ∂Measure.sum (sfiniteSeq μ)) at hh
  rwa [sum_sfiniteSeq] at hh

end ReciprocalXi

