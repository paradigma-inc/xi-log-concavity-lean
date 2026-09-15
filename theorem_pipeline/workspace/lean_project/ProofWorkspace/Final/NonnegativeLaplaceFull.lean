import ProofWorkspace.Final.FiniteLevyLawFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

def nonnegativeLaplace (ν : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, Real.exp (-x*y) ∂ν

theorem integrable_nonnegativeLaplace (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hn : ∀ᵐ y : ℝ ∂ν, 0≤y) {x : ℝ} (hx : 0≤x) :
    Integrable (fun y : ℝ ↦ Real.exp (-x*y)) ν := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [hn] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hy)

theorem nonnegativeLaplace_convolutionPower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hn : ∀ᵐ y : ℝ ∂ν, 0≤y) {x : ℝ} (hx : 0≤x) (n : ℕ) :
    nonnegativeLaplace (convolutionPower ν n) x=(nonnegativeLaplace ν x)^n := by
  induction n with
  | zero => simp [nonnegativeLaplace, convolutionPower]
  | succ n ih =>
    have hi := integrable_nonnegativeLaplace (convolutionPower ν (n+1))
      (ae_nonneg_convolutionPower ν hn (n+1)) hx
    rw [convolutionPower] at hi
    rw [nonnegativeLaplace, convolutionPower]
    rw [integral_conv hi]
    simp_rw [mul_add, Real.exp_add]
    rw [show (∫ a : ℝ, ∫ b : ℝ, Real.exp (-x*a)*Real.exp (-x*b)
        ∂convolutionPower ν n ∂ν)=
        (∫ a : ℝ, Real.exp (-x*a) ∂ν)*(∫ b : ℝ, Real.exp (-x*b) ∂convolutionPower ν n) by
      simp_rw [integral_const_mul]
      rw [integral_mul_const]]
    change nonnegativeLaplace ν x*nonnegativeLaplace (convolutionPower ν n) x=_
    rw [ih, pow_succ']

theorem hasSum_poisson_real_powers (r : ℝ≥0) (z : ℝ) :
    HasSum (fun n : ℕ ↦ poissonPMFReal r n*z^n) (Real.exp ((r:ℝ)*(z-1))) := by
  have hs := Complex.reCLM.hasSum (hasSum_poisson_complex_powers r (z:ℂ))
  simpa only [Complex.reCLM_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_exp,
    Complex.ofReal_re] using hs

theorem nonnegativeLaplace_compoundPoissonLaw (r : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hn : ∀ᵐ y : ℝ ∂ν, 0≤y) {x : ℝ} (hx : 0≤x) :
    nonnegativeLaplace (compoundPoissonLaw r ν) x=
      Real.exp ((r:ℝ)*(nonnegativeLaplace ν x-1)) := by
  have hi := integrable_nonnegativeLaplace (compoundPoissonLaw r ν)
    (ae_nonneg_compoundPoissonLaw r ν hn) hx
  rw [nonnegativeLaplace, compoundPoissonLaw, integral_sum_measure hi]
  have he (n : ℕ) : (∫ y : ℝ, Real.exp (-x*y)
      ∂(poissonPMF r n) • convolutionPower ν n)=
      poissonPMFReal r n*(nonnegativeLaplace ν x)^n := by
    rw [integral_smul_measure]
    change (ENNReal.ofReal (poissonPMFReal r n)).toReal*
      nonnegativeLaplace (convolutionPower ν n) x=_
    rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg,
      nonnegativeLaplace_convolutionPower ν hn hx]
  simp_rw [he]
  exact (hasSum_poisson_real_powers r (nonnegativeLaplace ν x)).tsum_eq

theorem nonnegativeLaplace_finiteLevyLaw (μ : FiniteMeasure ℝ)
    (hn : ∀ᵐ y : ℝ ∂(μ:Measure ℝ), 0≤y) {x : ℝ} (hx : 0≤x) :
    nonnegativeLaplace (finiteLevyLaw μ) x=
      Real.exp (∫ y : ℝ, Real.exp (-x*y)-1 ∂(μ:Measure ℝ)) := by
  by_cases h0 : μ=0
  · subst μ
    simp [finiteLevyLaw_zero, nonnegativeLaplace]
  have hn' : ∀ᵐ y : ℝ ∂(μ.normalize:Measure ℝ), 0≤y := by
    rw [μ.toMeasure_normalize_eq_of_nonzero h0]
    exact ae_smul_measure hn _
  rw [finiteLevyLaw, nonnegativeLaplace_compoundPoissonLaw μ.mass _ hn' hx]
  congr 1
  rw [finiteMeasure_eq_mass_smul_normalize μ, integral_smul_nnreal_measure,
    integral_sub (integrable_nonnegativeLaplace _ hn' hx) (integrable_const 1)]
  simp [nonnegativeLaplace, NNReal.smul_def, smul_eq_mul]

end ReciprocalXi

