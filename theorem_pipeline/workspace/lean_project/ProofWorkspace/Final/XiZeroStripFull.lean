import ProofWorkspace.Final.XiMellinIdentityFull
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Actual Xi zero-free strip and the reciprocal analytic extension

The strip is proved from the actual theta rectangle, the convergent zeta
half-plane, and Xi's functional equation. No strip decay bound is assumed.
-/

noncomputable section
open Set
namespace ReciprocalXi

/-- Actual Xi cannot vanish in the absolutely convergent zeta half-plane. -/
theorem xi_ne_zero_of_one_lt_re (s : ℂ) (hs : 1 < s.re) : xi s ≠ 0 := by
  have h0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have h1 : s ≠ 1 := by
    intro h
    simp only [h, Complex.one_re, lt_self_iff_false] at hs
  have hg : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hc : completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s :=
    ((eq_div_iff hg).mp (riemannZeta_def_of_ne_zero h0)).symm
  rw [xi_eq_completed s h0 h1, hc]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    (mul_ne_zero hz hg)) (by norm_num)

theorem xi_ne_zero_of_re_lt_zero (s : ℂ) (hs : s.re < 0) : xi s ≠ 0 := by
  have h := xi_ne_zero_of_one_lt_re (1 - s) (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  simpa only [xi_one_sub] using h

/-- An unconditional horizontal zero-free strip for the actual Xi function.
No restriction on the real part is needed. -/
theorem xi_ne_zero_of_abs_im_le_half (s : ℂ) (hs : |s.im| ≤ 1 / 2) : xi s ≠ 0 := by
  by_cases h0 : s.re < 0
  · exact xi_ne_zero_of_re_lt_zero s h0
  · by_cases h1 : 1 < s.re
    · exact xi_ne_zero_of_one_lt_re s h1
    · exact xi_ne_zero_of_central_rectangle s (le_of_not_gt h0) (le_of_not_gt h1) hs

/-- The exact complex-variable counterpart of the real-axis normalization. -/
theorem F_imaginary_axis_complex (z : ℂ) :
    F (Complex.I * z) = xi ((1 + z) / 2) / 4 := by
  unfold F
  have h : (1 / 2 + Complex.I * (Complex.I * z) / 2 : ℂ) =
      1 - ((1 + z) / 2) := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  rw [h, xi_one_sub]

theorem F_imaginary_axis_complex_ne_zero (z : ℂ) (hz : |z.im| ≤ 1) :
    F (Complex.I * z) ≠ 0 := by
  rw [F_imaginary_axis_complex]
  apply div_ne_zero
  · apply xi_ne_zero_of_abs_im_le_half
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.one_im, zero_add,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · norm_num

/-- Complex extension of the actual normalized reciprocal Fourier transform. -/
def reciprocalExtension (z : ℂ) : ℂ := F 0 / F (Complex.I * z)

theorem reciprocalExtension_ofReal (u : ℝ) :
    reciprocalExtension (u : ℂ) = reciprocalTransform u := rfl

theorem reciprocalExtension_eq_xi_ratio (z : ℂ) :
    reciprocalExtension z = xi (1 / 2) / xi ((1 + z) / 2) := by
  rw [reciprocalExtension, F_imaginary_axis_complex]
  have h0 : F 0 = xi (1 / 2) / 4 := by simp [F]
  rw [h0]
  ring

theorem differentiable_F_complex : Differentiable ℂ F := by
  have harg : Differentiable ℂ (fun z : ℂ => 1 / 2 + Complex.I * z / 2) := by
    fun_prop
  exact (differentiable_xi.comp harg).div_const 4

/-- Holomorphy at every point of the open strip |Im z|<1. -/
theorem differentiableAt_reciprocalExtension (z : ℂ) (hz : |z.im| < 1) :
    DifferentiableAt ℂ reciprocalExtension z := by
  have hden : Differentiable ℂ (fun w : ℂ => F (Complex.I * w)) :=
    differentiable_F_complex.comp ((differentiable_const Complex.I).mul differentiable_id)
  exact ((differentiable_const (F 0)).differentiableAt).div
    (hden z) (F_imaginary_axis_complex_ne_zero z hz.le)

theorem differentiableOn_reciprocalExtension :
    DifferentiableOn ℂ reciprocalExtension {z : ℂ | |z.im| < 1} := by
  intro z hz
  exact (differentiableAt_reciprocalExtension z hz).differentiableWithinAt

end ReciprocalXi

end
