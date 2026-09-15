import ProofWorkspace.Final.GammaVerticalBoundsFull
import ProofWorkspace.Final.ZetaVerticalBoundsFull
import ProofWorkspace.Final.XiStripBoundsFull
import ProofWorkspace.Final.RationalExpBoundsFull

/-!
# A quantitative closed-strip bound for the actual reciprocal transform

The outer region is derived from the actual Xi factorization and proved
Gamma/zeta estimates, and joined to the actual central theta estimate.
-/

noncomputable section
namespace ReciprocalXi

theorem exp_sixteenth_le_five_fourths : Real.exp ((1 : ℝ) / 16) ≤ 5 / 4 := by
  have h := (ratExp_enclosure (1 / 16) 2 (by norm_num) (by norm_num)).2
  norm_num [ratExpTaylor, ratExpError, Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem Gamma_half_vertical_norm_comparison (s : ℂ)
    (hs : 2 ≤ s.re) (hi : |s.im| ≤ 1 / 2) :
    ‖Complex.Gamma ((s.re : ℂ) / 2)‖ ≤ (5 / 4 : ℝ) * ‖Complex.Gamma (s / 2)‖ := by
  have hx : 1 ≤ s.re / 2 := by linarith
  have ht : (s.im / 2) ^ 2 ≤ 1 / 16 := by
    have hi' := abs_le.mp hi
    nlinarith [sq_nonneg (s.im / 2),
      mul_nonneg (by linarith : 0 ≤ 1 / 2 - s.im)
        (by linarith : 0 ≤ 1 / 2 + s.im)]
  have he : Real.exp ((s.im / 2) ^ 2) ≤ 5 / 4 :=
    (Real.exp_le_exp.mpr ht).trans exp_sixteenth_le_five_fourths
  have hid : ((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * Complex.I = s / 2 := by
    apply Complex.ext <;> simp
  have hratio := gamma_vertical_ratio_le_exp (s.re / 2) (s.im / 2) hx
  rw [hid] at hratio
  have hp : 0 < ‖Complex.Gamma (s / 2)‖ := by
    have h := gamma_vertical_lower_bound (s.re / 2) (s.im / 2) hx
    rw [hid] at h
    exact lt_of_lt_of_le
      (mul_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.exp_pos _)) h
  have hh := (div_le_iff₀ hp).mp (hratio.trans he)
  have hr : ‖Complex.Gamma ((s.re : ℂ) / 2)‖ = Real.Gamma (s.re / 2) := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_div, Complex.Gamma_ofReal,
      Complex.norm_of_nonneg (Real.Gamma_pos_of_pos (by linarith)).le]
  rwa [hr]

theorem xi_norm_eq_factors_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    ‖xi s‖ = ‖s‖ * ‖s - 1‖ *
      (Real.pi ^ (-s.re / 2) * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖) / 2 := by
  have h0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have h1 : s ≠ 1 := by
    intro h
    simp only [h, Complex.one_re, lt_self_iff_false] at hs
  have hg : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hc : completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s :=
    ((eq_div_iff hg).mp (riemannZeta_def_of_ne_zero h0)).symm
  rw [xi_eq_completed s h0 h1, hc, Complex.Gammaℝ_def]
  simp only [norm_div, norm_mul, Complex.norm_ofNat,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.div_ofNat_re,
    Complex.neg_re]
  ring

/-- Actual Xi comparison in the entire outer part of the half-height strip. -/
theorem xi_vertical_norm_comparison_outer (s : ℂ)
    (hs : 2 ≤ s.re) (hi : |s.im| ≤ 1 / 2) :
    ‖xi (s.re : ℂ)‖ ≤ 5 * ‖xi s‖ := by
  have hgamma := Gamma_half_vertical_norm_comparison s hs hi
  have hzeta := riemannZeta_vertical_norm_comparison s hs
  have hlin : ‖(s.re : ℂ)‖ ≤ ‖s‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm s
  have hlin' : ‖(s.re : ℂ) - 1‖ ≤ ‖s - 1‖ := by
    simpa only [Complex.sub_re, Complex.one_re, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
      Complex.abs_re_le_norm (s - 1)
  rw [xi_norm_eq_factors_of_one_lt_re _ (by simpa using (show 1 < s.re by linarith)),
    xi_norm_eq_factors_of_one_lt_re s (by linarith)]
  simp only [Complex.ofReal_re]
  calc
    _ ≤ ‖s‖ * ‖s - 1‖ *
        (Real.pi ^ (-s.re / 2) * ((5 / 4) * ‖Complex.Gamma (s / 2)‖) *
          (4 * ‖riemannZeta s‖)) / 2 := by
      gcongr
    _ = _ := by ring

/-- Reciprocal comparison on the right tail of the closed unit strip. -/
theorem reciprocalExtension_norm_le_five_right (z : ℂ)
    (hr : 3 ≤ z.re) (hi : |z.im| ≤ 1) :
    ‖reciprocalExtension z‖ ≤ 5 * ‖reciprocalTransform z.re‖ := by
  let s : ℂ := (1 + z) / 2
  have hs : 2 ≤ s.re := by
    simp only [s, Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith
  have hsi : |s.im| ≤ 1 / 2 := by
    simp only [s, Complex.div_ofNat_im, Complex.add_im, Complex.one_im,
      zero_add, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hsr : (s.re : ℂ) = (1 + (z.re : ℂ)) / 2 := by
    simp only [s, Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    push_cast
    rfl
  have hp : 0 < ‖xi (s.re : ℂ)‖ := norm_pos_iff.mpr
    (xi_ne_zero_of_abs_im_le_half (s.re : ℂ) (by simp))
  have hc := xi_vertical_norm_comparison_outer s hs hsi
  have hd : ‖xi (s.re : ℂ)‖ / 5 ≤ ‖xi s‖ := by linarith
  have hb := div_le_div_of_nonneg_left (norm_nonneg (xi (1 / 2)))
    (div_pos hp (by norm_num : (0 : ℝ) < 5)) hd
  have he : ‖xi (1 / 2)‖ / (‖xi (s.re : ℂ)‖ / 5) =
      5 * (‖xi (1 / 2)‖ / ‖xi (s.re : ℂ)‖) := by ring
  rw [he] at hb
  change ‖reciprocalExtension z‖ ≤ 5 * ‖reciprocalExtension (z.re : ℂ)‖
  rw [reciprocalExtension_eq_xi_ratio, reciprocalExtension_eq_xi_ratio,
    norm_div, norm_div]
  rw [hsr] at hb
  exact hb

theorem reciprocalExtension_even (z : ℂ) :
    reciprocalExtension (-z) = reciprocalExtension z := by
  simp only [reciprocalExtension, mul_neg, F_even]

/-- Uniform quantitative comparison throughout the actual closed unit strip.
There is no restriction on the real part and no additional analytic premise. -/
theorem reciprocalExtension_norm_le_five (z : ℂ) (hi : |z.im| ≤ 1) :
    ‖reciprocalExtension z‖ ≤ 5 * ‖reciprocalTransform z.re‖ := by
  by_cases hc : |z.re| ≤ 3
  · have h := reciprocalExtension_norm_le_two_central z hc hi
    linarith [norm_nonneg (reciprocalTransform z.re)]
  · have hr : 3 ≤ |z.re| := (lt_of_not_ge hc).le
    by_cases hp : 0 ≤ z.re
    · rw [abs_of_nonneg hp] at hr
      exact reciprocalExtension_norm_le_five_right z hr hi
    · rw [abs_of_neg (lt_of_not_ge hp)] at hr
      have h := reciprocalExtension_norm_le_five_right (-z)
        (by simpa only [Complex.neg_re] using hr)
        (by simpa only [Complex.neg_im, abs_neg] using hi)
      simpa only [reciprocalExtension_even, Complex.neg_re, reciprocalTransform_even] using h

/-- The real-axis decay bound now also controls every horizontal line in the
closed strip, uniformly in its height. -/
theorem reciprocalExtension_norm_le_exp_of_abs_re_three_le (z : ℂ) (r : ℝ)
    (hr : 3 ≤ |z.re|) (hi : |z.im| ≤ 1) :
    ‖reciprocalExtension z‖ ≤
      5 * reciprocalTailConstant r * Real.exp (-(r * |z.re|)) := by
  have h := (reciprocalExtension_norm_le_five z hi).trans
    (mul_le_mul_of_nonneg_left
      (reciprocalTransform_norm_le_exp_of_abs_three_le z.re r hr)
      (by norm_num : (0 : ℝ) ≤ 5))
  simpa only [mul_assoc] using h

end ReciprocalXi
