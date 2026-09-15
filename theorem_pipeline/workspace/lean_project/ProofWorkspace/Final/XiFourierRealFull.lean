import ProofWorkspace.Final.XiFourierJetsFull
import ProofWorkspace.Final.XiZeroStripFull
import Mathlib.MeasureTheory.Group.Integral

/-!
# Reality of the actual reciprocal-Xi Fourier density

Reality is proved from the actual special-function formulas and Fourier
reflection. The positive value at the origin is not a global positivity claim.
-/

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace ReciprocalXi

theorem thetaMellinIntegrand_ofReal (s t : ℝ) (ht : 0 < t) :
    thetaMellinIntegrand (s : ℂ) t =
      ((t ^ (s - 1) * (HurwitzZeta.cosKernel 0 t - 1) : ℝ) : ℂ) := by
  unfold thetaMellinIntegrand
  have he : (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_cpow ht.le]
  push_cast
  rfl

theorem thetaMellinIntegral_conj_ofReal (s : ℝ) :
    conj (∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s : ℂ) t) =
      ∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s : ℂ) t := by
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have he := thetaMellinIntegrand_ofReal s t (lt_trans zero_lt_one ht)
  change conj (thetaMellinIntegrand (s : ℂ) t) = thetaMellinIntegrand (s : ℂ) t
  simp only [he, Complex.conj_ofReal]

theorem completedRiemannZeta₀_conj_ofReal_central (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    conj (completedRiemannZeta₀ (s : ℂ)) = completedRiemannZeta₀ (s : ℂ) := by
  rw [completedRiemannZeta₀_eq_thetaMellin (s : ℂ) hs.1 hs.2]
  have he1 : (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) := by push_cast; rfl
  have he2 : (1 - (s : ℂ)) / 2 = (((1 - s) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he1, he2]
  simp only [map_div₀, map_add, map_ofNat, thetaMellinIntegral_conj_ofReal]

/-- Reality follows from the actual special-function formulas, not an axiom. -/
theorem xi_conj_ofReal (s : ℝ) : conj (xi (s : ℂ)) = xi (s : ℂ) := by
  by_cases hs1 : 1 < s
  · rw [xi_ofReal_eq_of_one_lt s hs1]
    exact Complex.conj_ofReal _
  · by_cases hs0 : s < 0
    · rw [← xi_one_sub (s : ℂ)]
      have he : 1 - (s : ℂ) = ((1 - s : ℝ) : ℂ) := by push_cast; rfl
      rw [he, xi_ofReal_eq_of_one_lt (1 - s) (by linarith)]
      exact Complex.conj_ofReal _
    · have hc := completedRiemannZeta₀_conj_ofReal_central s
        ⟨le_of_not_gt hs0, le_of_not_gt hs1⟩
      simp only [xi, map_div₀, map_add, map_mul, map_sub, map_ofNat,
        map_one, Complex.conj_ofReal, hc]

theorem xi_ofReal_eq_re (s : ℝ) : xi (s : ℂ) = ((xi (s : ℂ)).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (xi_conj_ofReal s)).symm

theorem reciprocalTransform_eq_real_ratio (u : ℝ) :
    reciprocalTransform u =
      (((xi (((1 / 2 : ℝ) : ℂ))).re /
        (xi ((((1 + u) / 2 : ℝ) : ℂ))).re : ℝ) : ℂ) := by
  change reciprocalExtension (u : ℂ) = _
  rw [reciprocalExtension_eq_xi_ratio]
  have hnum : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hden : (1 + (u : ℂ)) / 2 = (((1 + u) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hnum, hden, xi_ofReal_eq_re (1 / 2), xi_ofReal_eq_re ((1 + u) / 2)]
  push_cast
  rfl

theorem reciprocalTransform_conj (u : ℝ) : conj (reciprocalTransform u) = reciprocalTransform u := by
  rw [reciprocalTransform_eq_real_ratio]
  simp

theorem reciprocalTransform_re_pos (u : ℝ) : 0 < (reciprocalTransform u).re := by
  rw [reciprocalTransform_eq_real_ratio, Complex.ofReal_re]
  exact div_pos (xi_re_pos (1 / 2)) (xi_re_pos ((1 + u) / 2))

theorem density_integrand_conj (x u : ℝ) :
    conj (reciprocalTransform u * Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))) =
      reciprocalTransform (-u) * Complex.exp (-Complex.I * (x : ℂ) * ((-u : ℝ) : ℂ)) := by
  simp only [map_mul, ← Complex.exp_conj, reciprocalTransform_conj,
    reciprocalTransform_even, map_neg, Complex.conj_I, Complex.conj_ofReal,
    neg_neg, Complex.ofReal_neg]
  congr 2
  ring

/-- Reflection in the Fourier variable cancels the imaginary part exactly. -/
theorem density_integral_conj (x : ℝ) :
    conj (∫ u : ℝ, reciprocalTransform u * Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))) =
      ∫ u : ℝ, reciprocalTransform u * Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ)) := by
  rw [← integral_conj]
  simp_rw [density_integrand_conj]
  exact integral_neg_eq_self
    (fun u : ℝ => reciprocalTransform u * Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ)))
    volume

/-- Taking the real part in the density definition discards nothing. -/
theorem density_eq_complex_integral (x : ℝ) :
    (density x : ℂ) =
      (∫ u : ℝ, reciprocalTransform u * Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))) /
        (2 * (Real.pi : ℂ)) := by
  have h := Complex.conj_eq_iff_re.mp (density_integral_conj x)
  unfold density
  push_cast
  rw [h]

theorem density_zero_eq_integral_re :
    density 0 = (∫ u : ℝ, (reciprocalTransform u).re) / (2 * Real.pi) := by
  unfold density
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  congr 1
  exact (integral_re integrable_reciprocalTransform).symm

/-- Positivity at the origin is actual, but is not global density positivity. -/
theorem density_zero_pos : 0 < density 0 := by
  rw [density_zero_eq_integral_re]
  apply div_pos _ (by positivity)
  apply integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp continuous_reciprocalTransform)
    integrable_reciprocalTransform.re
    (fun u => (reciprocalTransform_re_pos u).le)
    (ne_of_gt (reciprocalTransform_re_pos 0))

end ReciprocalXi
