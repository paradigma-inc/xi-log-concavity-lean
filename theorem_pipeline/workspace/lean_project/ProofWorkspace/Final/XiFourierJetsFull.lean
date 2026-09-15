import ProofWorkspace.Final.XiFourierFull

/-!
# Explicit integral jets of the actual reciprocal-Xi density

All weighted integrability comes from the proved actual Xi estimates.
The derivative normalization is derived from mathlib's Fourier theorem.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace ReciprocalXi

def densityJetWeight (n : ℕ) (u : ℝ) : ℂ :=
  (-Complex.I * (u : ℂ)) ^ n * reciprocalTransform u

def complexDensityJet (n : ℕ) (x : ℝ) : ℂ :=
  𝓕 (densityJetWeight n) (x / (2 * Real.pi))

def densityJet (n : ℕ) (x : ℝ) : ℝ :=
  (complexDensityJet n x).re / (2 * Real.pi)

theorem norm_densityJetWeight (n : ℕ) (u : ℝ) :
    ‖densityJetWeight n u‖ = ‖u‖ ^ n * ‖reciprocalTransform u‖ := by
  simp only [densityJetWeight, norm_mul, norm_pow, norm_neg,
    Complex.norm_I, Complex.norm_real, one_mul]

theorem continuous_densityJetWeight (n : ℕ) : Continuous (densityJetWeight n) := by
  have h := continuous_reciprocalTransform
  unfold densityJetWeight
  fun_prop

theorem integrable_densityJetWeight (n : ℕ) : Integrable (densityJetWeight n) := by
  apply (integrable_reciprocalTransform_moment n).mono'
  · exact (continuous_densityJetWeight n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => (norm_densityJetWeight n u).le)

theorem integrable_mul_densityJetWeight (n : ℕ) :
    Integrable (fun u : ℝ => u • densityJetWeight n u) := by
  apply (integrable_reciprocalTransform_moment (n + 1)).mono'
  · exact (continuous_id.smul (continuous_densityJetWeight n)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    simp only [norm_smul, norm_densityJetWeight, pow_succ]
    exact le_of_eq (by ring)

theorem fourier_derivative_densityJetWeight (n : ℕ) :
    (fun u : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) • densityJetWeight n u) =
      ((2 * Real.pi : ℝ) : ℂ) • densityJetWeight (n + 1) := by
  funext u
  simp only [densityJetWeight, Pi.smul_apply, smul_eq_mul, pow_succ]
  push_cast
  ring

theorem fourier_smul_densityJetWeight (n : ℕ) (c : ℂ) :
    𝓕 (c • densityJetWeight n) = c • 𝓕 (densityJetWeight n) := by
  funext x
  simp only [Real.fourier_real_eq_integral_exp_smul, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by ring)

/-- Consecutive integral jets are actual derivatives. The 2π factor in the
Fourier derivative cancels against the argument scaling x/(2π). -/
theorem hasDerivAt_complexDensityJet (n : ℕ) (x : ℝ) :
    HasDerivAt (complexDensityJet n) (complexDensityJet (n + 1) x) x := by
  have hf := Real.hasDerivAt_fourier (integrable_densityJetWeight n)
    (integrable_mul_densityJetWeight n) (x / (2 * Real.pi))
  rw [fourier_derivative_densityJetWeight, fourier_smul_densityJetWeight] at hf
  have hc := hf.scomp x ((hasDerivAt_id x).div_const (2 * Real.pi))
  convert hc using 1
  simp only [complexDensityJet, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem hasDerivAt_densityJet (n : ℕ) (x : ℝ) :
    HasDerivAt (densityJet n) (densityJet (n + 1) x) x := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_complexDensityJet n x)
  exact hr.div_const (2 * Real.pi)

theorem densityJet_zero (x : ℝ) : densityJet 0 x = density x := by
  rw [density_eq_re_fourier]
  have hw : densityJetWeight 0 = reciprocalTransform := by
    funext u
    simp [densityJetWeight]
  simp only [densityJet, complexDensityJet, hw]

theorem deriv_densityJet (n : ℕ) : deriv (densityJet n) = densityJet (n + 1) := by
  funext x
  exact (hasDerivAt_densityJet n x).deriv

theorem iterated_deriv_density_eq_densityJet (n : ℕ) :
    deriv^[n] density = densityJet n := by
  induction n with
  | zero =>
      funext x
      exact (densityJet_zero x).symm
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact deriv_densityJet n

/-- Exact integral formula before taking the real part; the frequency scale
and minus sign agree with the original inverse-density definition. -/
theorem complexDensityJet_eq_integral (n : ℕ) (x : ℝ) :
    complexDensityJet n x = ∫ u : ℝ, densityJetWeight n u *
      Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ)) := by
  rw [complexDensityJet, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  simp only [smul_eq_mul]
  rw [mul_comm (densityJetWeight n u)]
  congr 2
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem densityJet_eq_integral (n : ℕ) (x : ℝ) :
    densityJet n x =
      (∫ u : ℝ, (-Complex.I * (u : ℂ)) ^ n * reciprocalTransform u *
        Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))).re / (2 * Real.pi) := by
  rw [densityJet, complexDensityJet_eq_integral]
  rfl

/-- All actual iterated derivatives have the expected absolutely convergent
Fourier integral. There are no differentiability or moment premises. -/
theorem iterated_deriv_density_eq_integral (n : ℕ) (x : ℝ) :
    (deriv^[n] density) x =
      (∫ u : ℝ, (-Complex.I * (u : ℂ)) ^ n * reciprocalTransform u *
        Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))).re / (2 * Real.pi) := by
  rw [iterated_deriv_density_eq_densityJet, densityJet_eq_integral]

theorem deriv_density_eq_integral (x : ℝ) :
    deriv density x =
      (∫ u : ℝ, (-Complex.I * (u : ℂ)) * reciprocalTransform u *
        Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))).re / (2 * Real.pi) := by
  simpa only [Function.iterate_one, pow_one] using iterated_deriv_density_eq_integral 1 x

theorem second_deriv_density_eq_integral (x : ℝ) :
    deriv (deriv density) x =
      (∫ u : ℝ, -((u : ℂ) ^ 2) * reciprocalTransform u *
        Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))).re / (2 * Real.pi) := by
  have h := iterated_deriv_density_eq_integral 2 x
  have hp (u : ℝ) : (-Complex.I * (u : ℂ)) ^ 2 = -((u : ℂ) ^ 2) := by
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  simpa only [Function.iterate_succ_apply', Function.iterate_one, hp] using h

theorem norm_densityJet_integrand (n : ℕ) (x u : ℝ) :
    ‖densityJetWeight n u * Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))‖ =
      ‖u‖ ^ n * ‖reciprocalTransform u‖ := by
  rw [norm_mul, norm_densityJetWeight, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem integrable_densityJet_integrand (n : ℕ) (x : ℝ) :
    Integrable (fun u : ℝ => densityJetWeight n u *
      Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))) := by
  apply (integrable_reciprocalTransform_moment n).mono'
  · have hw := continuous_densityJetWeight n
    exact (by fun_prop : Continuous (fun u : ℝ => densityJetWeight n u *
      Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => (norm_densityJet_integrand n x u).le)

end ReciprocalXi

end
