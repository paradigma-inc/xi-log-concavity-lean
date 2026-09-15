import ProofWorkspace.Final.XiMellinIdentityFull
import ProofWorkspace.Final.XiZeroStripFull
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Quantitative central reciprocal-Xi strip estimate

The actual theta representation supplies numerical norm bounds throughout
a wide rectangle; these control the magnitude of the actual reciprocal,
not only its nonvanishing.
-/

noncomputable section
open MeasureTheory Set
namespace ReciprocalXi

/-- The actual theta/Mellin formula holds on the larger closed strip. -/
theorem completedRiemannZeta₀_eq_thetaMellin_wide (s : ℂ)
    (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 2) :
    completedRiemannZeta₀ s =
      ((∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s / 2) t) +
        ∫ t : ℝ in Ioi 1, thetaMellinIntegrand ((1 - s) / 2) t) / 2 := by
  have hσ : (s / 2).re ≤ 1 := by simp only [Complex.div_ofNat_re]; linarith
  have hσ' : ((1 / 2 : ℂ) - s / 2).re ≤ 1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  unfold completedRiemannZeta₀ HurwitzZeta.completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  rw [mellin_hurwitzZero_f_modif (s / 2) hσ hσ', mellin_upperThetaKernel,
    mellin_upperThetaKernel]
  rw [show (1 / 2 : ℂ) - s / 2 = (1 - s) / 2 by ring]

theorem completedRiemannZeta₀_norm_le_thetaBound_wide (s : ℂ)
    (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ ≤ 4 * Real.exp (-Real.pi) / Real.pi := by
  have hσ : (s / 2).re ≤ 1 := by simp only [Complex.div_ofNat_re]; linarith
  have hσ' : ((1 - s) / 2).re ≤ 1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have h₁ := thetaMellinIntegral_norm_le (s / 2) hσ
  have h₂ := thetaMellinIntegral_norm_le ((1 - s) / 2) hσ'
  have hsum := norm_add_le
    (∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s / 2) t)
    (∫ t : ℝ in Ioi 1, thetaMellinIntegrand ((1 - s) / 2) t)
  rw [completedRiemannZeta₀_eq_thetaMellin_wide s hs0 hs1, norm_div]
  norm_num only [Complex.norm_ofNat]
  linarith

theorem thetaBound_lt_one_eighth : 4 * Real.exp (-Real.pi) / Real.pi < 1 / 8 := by
  have he1 : (5 : ℝ) / 2 ≤ Real.exp 1 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at h
    linarith
  have he3 : (125 : ℝ) / 8 ≤ Real.exp 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2) he1 3
    have he : Real.exp 1 ^ 3 = Real.exp 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he] at h
    norm_num at h
    exact h
  have hep : (125 : ℝ) / 8 < Real.exp Real.pi :=
    he3.trans_lt (Real.exp_lt_exp.mpr Real.pi_gt_three)
  have hi : Real.exp (-Real.pi) < 8 / 125 := by
    rw [Real.exp_neg, ← one_div]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    linarith
  apply (div_lt_iff₀ Real.pi_pos).mpr
  linarith [Real.pi_gt_three]

theorem completedRiemannZeta₀_norm_lt_one_eighth (s : ℂ)
    (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ < 1 / 8 :=
  (completedRiemannZeta₀_norm_le_thetaBound_wide s hs0 hs1).trans_lt
    thetaBound_lt_one_eighth

theorem xi_quadratic_factor_norm_le_wide (s : ℂ)
    (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 2) (hi : |s.im| ≤ 1 / 2) :
    ‖s * (s - 1)‖ ≤ 11 / 4 := by
  have hq : s.re * (s.re - 1) ≤ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s.re + 1) (by linarith : 0 ≤ 2 - s.re)]
  have hi' := abs_le.mp hi
  have hisq : s.im ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - s.im)
      (by linarith : 0 ≤ 1 / 2 + s.im)]
  have hsn : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have htn : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    ring
  rw [norm_mul]
  nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖)]

/-- A uniform positive lower bound for the actual Xi in the wide rectangle. -/
theorem xi_re_ge_wide_rectangle (s : ℂ)
    (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 2) (hi : |s.im| ≤ 1 / 2) :
    21 / 64 ≤ (xi s).re := by
  have hp := xi_quadratic_factor_norm_le_wide s hs0 hs1 hi
  have hz := (completedRiemannZeta₀_norm_lt_one_eighth s hs0 hs1).le
  have ha : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤ 11 / 32 := by
    rw [norm_mul]
    calc
      _ ≤ (11 / 4 : ℝ) * (1 / 8) :=
        mul_le_mul hp hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 11 / 4)
      _ = _ := by norm_num
  have hr := Complex.re_le_norm (-(s * (s - 1) * completedRiemannZeta₀ s))
  simp only [Complex.neg_re, norm_neg] at hr
  have hx : (xi s).re = ((s * (s - 1) * completedRiemannZeta₀ s).re + 1) / 2 := by
    simp only [xi, Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
  rw [hx]
  linarith

theorem xi_norm_le_real_wide (x : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 2) :
    ‖xi (x : ℂ)‖ ≤ 5 / 8 := by
  have hq : |x * (x - 1)| ≤ 2 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (x - 1 / 2)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ x + 1) (by linarith : 0 ≤ 2 - x)]
  have hqc : ‖(x : ℂ) * ((x : ℂ) - 1)‖ ≤ 2 := by
    norm_cast
  have hz := (completedRiemannZeta₀_norm_lt_one_eighth (x : ℂ) hx0 hx1).le
  have hp : ‖(x : ℂ) * ((x : ℂ) - 1) * completedRiemannZeta₀ (x : ℂ)‖ ≤ 1 / 4 := by
    rw [norm_mul]
    calc
      _ ≤ (2 : ℝ) * (1 / 8) :=
        mul_le_mul hqc hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      _ = _ := by norm_num
  have ha := norm_add_le ((x : ℂ) * ((x : ℂ) - 1) * completedRiemannZeta₀ (x : ℂ)) 1
  rw [xi, norm_div]
  norm_num only [Complex.norm_ofNat]
  norm_num only [norm_one] at ha
  linarith

/-- The central strip estimate controls magnitude, not only nonvanishing. -/
theorem xi_norm_comparison_wide (s : ℂ)
    (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 2) (hi : |s.im| ≤ 1 / 2) :
    ‖xi (s.re : ℂ)‖ ≤ 2 * ‖xi s‖ := by
  have hl := (xi_re_ge_wide_rectangle s hs0 hs1 hi).trans (Complex.re_le_norm (xi s))
  have hu := xi_norm_le_real_wide s.re hs0 hs1
  linarith

/-- Quantitative control of the actual reciprocal transform in the central
part of the closed strip, with a constant stronger than the source's five. -/
theorem reciprocalExtension_norm_le_two_central (z : ℂ)
    (hr : |z.re| ≤ 3) (hi : |z.im| ≤ 1) :
    ‖reciprocalExtension z‖ ≤ 2 * ‖reciprocalTransform z.re‖ := by
  let s : ℂ := (1 + z) / 2
  have hr' := abs_le.mp hr
  have hs0 : -1 ≤ s.re := by
    simp only [s, Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith
  have hs1 : s.re ≤ 2 := by
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
  have hc := xi_norm_comparison_wide s hs0 hs1 hsi
  have hd : ‖xi (s.re : ℂ)‖ / 2 ≤ ‖xi s‖ := by linarith
  have hb := div_le_div_of_nonneg_left (norm_nonneg (xi (1 / 2)))
    (half_pos hp) hd
  have he : ‖xi (1 / 2)‖ / (‖xi (s.re : ℂ)‖ / 2) =
      2 * (‖xi (1 / 2)‖ / ‖xi (s.re : ℂ)‖) := by ring
  rw [he] at hb
  change ‖reciprocalExtension z‖ ≤ 2 * ‖reciprocalExtension (z.re : ℂ)‖
  rw [reciprocalExtension_eq_xi_ratio, reciprocalExtension_eq_xi_ratio,
    norm_div, norm_div]
  rw [hsr] at hb
  exact hb

end ReciprocalXi
