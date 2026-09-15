import ProofWorkspace.Final.CompoundPoissonFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem ae_nonneg_convolutionPower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ y ∂ν, 0≤y) (n : ℕ) : ∀ᵐ y ∂convolutionPower ν n, 0≤y := by
  induction n with
  | zero => simp [convolutionPower]
  | succ n ih =>
    rw [convolutionPower, Measure.conv, ae_map_iff (by fun_prop) measurableSet_Ici]
    filter_upwards [quasiMeasurePreserving_fst.ae hν, quasiMeasurePreserving_snd.ae ih]
      with p hp hq
    exact add_nonneg hp hq

theorem ae_nonneg_compoundPoissonLaw (r : ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ y ∂ν, 0≤y) : ∀ᵐ y ∂compoundPoissonLaw r ν, 0≤y := by
  rw [compoundPoissonLaw, ae_sum_iff]
  intro n
  exact ae_smul_measure (ae_nonneg_convolutionPower ν hν n) _

theorem hasSum_poisson_nat_moment (r : ℝ≥0) :
    HasSum (fun n : ℕ ↦ poissonPMFReal r n*(n:ℝ)) (r:ℝ) := by
  have he (n : ℕ) : poissonPMFReal r (n+1)*((n+1:ℕ):ℝ) =
      (r:ℝ)*poissonPMFReal r n := by
    simp only [poissonPMFReal, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hn : ((n+1:ℕ):ℝ)≠0 := by positivity
    field_simp
  have hs := (poissonPMFRealSum r).mul_left (r:ℝ)
  rw [mul_one] at hs
  have hh : HasSum (fun n : ℕ ↦ poissonPMFReal r (n+1)*((n+1:ℕ):ℝ)) (r:ℝ) := by
    simpa only [he] using hs
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, add_zero] using
    (hasSum_nat_add_iff (f:=fun n : ℕ ↦ poissonPMFReal r n*(n:ℝ)) 1).mp hh

theorem integrable_id_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) : Integrable id (μ ∗ ν) := by
  rw [Measure.conv]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact (hμ.comp_fst ν).add (hν.comp_snd μ)

theorem integral_norm_conv_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) :
    (∫ y : ℝ, ‖y‖ ∂(μ ∗ ν)) ≤ (∫ y : ℝ, ‖y‖ ∂μ)+(∫ y : ℝ, ‖y‖ ∂ν) := by
  have hi : Integrable (fun y : ℝ ↦ ‖y‖) (μ ∗ ν) := (integrable_id_conv μ ν hμ hν).norm
  have hμn : Integrable (fun y : ℝ ↦ ‖y‖) μ := hμ.norm
  have hνn : Integrable (fun y : ℝ ↦ ‖y‖) ν := hν.norm
  rw [integral_conv hi]
  calc
    _ ≤ ∫ x : ℝ, ∫ y : ℝ, ‖x‖+‖y‖ ∂ν ∂μ := by
      apply integral_mono (integrable_id_conv μ ν hμ hν |>.norm |>.comp_aemeasurable
        (show AEMeasurable (fun p : ℝ×ℝ ↦ p.1+p.2) (μ.prod ν) by fun_prop)
        |>.integral_prod_left)
        (((hμ.norm.comp_fst ν).add (hν.norm.comp_snd μ)).integral_prod_left)
      intro x
      apply integral_mono ((integrable_const x).add hν).norm
        ((integrable_const ‖x‖).add hν.norm)
      intro y
      exact norm_add_le x y
    _ = _ := by
      simp_rw [integral_add (integrable_const _) hνn, integral_const,
        measureReal_univ_eq_one, one_smul]
      rw [integral_add hμn (integrable_const _)]
      simp

theorem integrable_id_convolutionPower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable id ν) (n : ℕ) : Integrable id (convolutionPower ν n) := by
  induction n with
  | zero => exact integrable_dirac (f:=id) (a:=(0:ℝ)) (by simp)
  | succ n ih => exact integrable_id_conv ν (convolutionPower ν n) hν ih

theorem integral_norm_convolutionPower_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable id ν) (n : ℕ) :
    (∫ y : ℝ, ‖y‖ ∂convolutionPower ν n) ≤ (n:ℝ)*(∫ y : ℝ, ‖y‖ ∂ν) := by
  induction n with
  | zero => simp [convolutionPower]
  | succ n ih =>
    have he := integral_norm_conv_le ν (convolutionPower ν n) hν
      (integrable_id_convolutionPower ν hν n)
    change (∫ y : ℝ, ‖y‖ ∂ν ∗ convolutionPower ν n) ≤ _
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

theorem lintegral_norm_compoundPoissonLaw_le (r : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : Integrable id ν) :
    (∫⁻ y : ℝ, ‖y‖ₑ ∂compoundPoissonLaw r ν) ≤
      ENNReal.ofReal ((r:ℝ)*(∫ y : ℝ, ‖y‖ ∂ν)) := by
  have hm : 0≤∫ y : ℝ, ‖y‖ ∂ν := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hi (n : ℕ) : Integrable (fun y : ℝ ↦ y) (convolutionPower ν n) :=
    integrable_id_convolutionPower ν hν n
  rw [compoundPoissonLaw, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul,
    ← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  calc
    _ ≤ ∑' n : ℕ, (poissonPMF r n)*ENNReal.ofReal ((n:ℝ)*(∫ y : ℝ, ‖y‖ ∂ν)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal
        (integral_norm_convolutionPower_le ν hν n)) _
    _ = ∑' n : ℕ, ENNReal.ofReal (poissonPMFReal r n*(n:ℝ)*(∫ y : ℝ, ‖y‖ ∂ν)) := by
      apply tsum_congr
      intro n
      change ENNReal.ofReal (poissonPMFReal r n)*ENNReal.ofReal _ = _
      rw [← ENNReal.ofReal_mul poissonPMFReal_nonneg, mul_assoc]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n : ℕ ↦ mul_nonneg (mul_nonneg poissonPMFReal_nonneg (Nat.cast_nonneg n)) hm)
        ((hasSum_poisson_nat_moment r).summable.mul_right _),
        ((hasSum_poisson_nat_moment r).mul_right (∫ y : ℝ, ‖y‖ ∂ν)).tsum_eq]

theorem integrable_id_compoundPoissonLaw (r : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : Integrable id ν) :
    Integrable id (compoundPoissonLaw r ν) := by
  refine ⟨by fun_prop, ?_⟩
  exact (lintegral_norm_compoundPoissonLaw_le r ν hν).trans_lt ENNReal.ofReal_lt_top

end ReciprocalXi
