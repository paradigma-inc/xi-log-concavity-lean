import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
Actual Xi and reciprocal Fourier-density definitions, including removable values.
This module does NOT prove positivity, integrability, or log concavity of the density.
-/

noncomputable section
open MeasureTheory

namespace ReciprocalXi

/-- Standard entire xi, using mathlib's pole-removed completed zeta. -/
def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

theorem xi_zero : xi 0 = 1 / 2 := by simp [xi]

theorem xi_one : xi 1 = 1 / 2 := by simp [xi]

theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

/-- Agreement with the usual formula away from the removable points. -/
theorem xi_eq_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  unfold xi
  have h10 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

theorem differentiable_xi : Differentiable ℂ xi := by
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).div_const 2

/-- The normalization in the reviewed proof: F(z) = Xi(z/2)/4. -/
def F (z : ℂ) : ℂ := xi (1 / 2 + Complex.I * z / 2) / 4

theorem F_even (z : ℂ) : F (-z) = F z := by
  unfold F
  have h : (1 / 2 + Complex.I * (-z) / 2 : ℂ) =
      1 - (1 / 2 + Complex.I * z / 2) := by ring
  rw [h, xi_one_sub]

/-- Functional-equation conversion to the real zeta argument used in the certificate. -/
theorem F_imaginary_axis (u : ℝ) :
    F (Complex.I * (u : ℂ)) = xi ((1 + (u : ℂ)) / 2) / 4 := by
  unfold F
  have h : (1 / 2 + Complex.I * (Complex.I * (u : ℂ)) / 2 : ℂ) =
      1 - ((1 + (u : ℂ)) / 2) := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  rw [h, xi_one_sub]

/-- Normalized reciprocal transform on the real Fourier variable.
Nonvanishing of the denominator is a remaining analytic obligation. -/
def reciprocalTransform (u : ℝ) : ℂ := F 0 / F (Complex.I * (u : ℂ))

theorem reciprocalTransform_even (u : ℝ) :
    reciprocalTransform (-u) = reciprocalTransform u := by
  simp only [reciprocalTransform, Complex.ofReal_neg, mul_neg, F_even]

/-- Real inverse Fourier density with the exact frequency normalization.
The Bochner integral is total; its integrability must be proved separately. -/
def density (x : ℝ) : ℝ :=
  (∫ u : ℝ, reciprocalTransform u *
    Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ))).re / (2 * Real.pi)

end ReciprocalXi
