import ProofWorkspace.Final.XiDefinitionFull
import ProofWorkspace.Final.CurvatureBoundsFull
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
Reflection symmetry of the actual reciprocal-Xi inverse Fourier expression.
These results do not establish integrability, nonvanishing or differentiability.
They hold with mathlib's total integral and total derivative conventions.
-/

noncomputable section
open MeasureTheory
namespace ReciprocalXi

/-- Reflection of both space and frequency leaves the inverse Fourier integrand unchanged. -/
theorem density_integrand_reflection (x u : ℝ) :
    reciprocalTransform (-u) * Complex.exp (-Complex.I * ((-x : ℝ) : ℂ) * ((-u : ℝ) : ℂ)) =
      reciprocalTransform u * Complex.exp (-Complex.I * (x : ℂ) * (u : ℂ)) := by
  rw [reciprocalTransform_even]
  simp only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]

/-- Actual density evenness from the symmetry of the defining Fourier integral. -/
theorem density_even (x : ℝ) : density (-x) = density x := by
  have hi := integral_neg_eq_self
    (fun u : ℝ => reciprocalTransform u *
      Complex.exp (-Complex.I * ((-x : ℝ) : ℂ) * (u : ℂ))) volume
  simp only [density_integrand_reflection] at hi
  unfold density
  rw [← hi]

/-- Derivative parity under reflection, including nondifferentiable points. -/
theorem deriv_odd_of_even (f : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have heq : (fun y => f (-y)) = f := funext hf
  have hd := deriv_comp_neg f x
  rw [heq] at hd
  linarith

theorem deriv_even_of_odd (f : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) (x : ℝ) :
    deriv f (-x) = deriv f x := by
  have heq : (fun y => f (-y)) = fun y => -f y := funext hf
  have hd := deriv_comp_neg f x
  rw [heq] at hd
  change deriv (-f) x = -deriv f (-x) at hd
  rw [deriv.neg] at hd
  linarith

theorem density_deriv_odd (x : ℝ) : deriv density (-x) = -deriv density x :=
  deriv_odd_of_even density density_even x

theorem density_second_deriv_even (x : ℝ) :
    deriv (deriv density) (-x) = deriv (deriv density) x :=
  deriv_even_of_odd (deriv density) density_deriv_odd x

/-- The actual curvature expression is even; this discharges the reflection
premise in compact-plus-tail gluing, but does not supply either positivity bound. -/
theorem density_curvature_even (x : ℝ) :
    curvatureJet (density (-x)) (deriv density (-x)) (deriv (deriv density) (-x)) =
      curvatureJet (density x) (deriv density x) (deriv (deriv density) x) := by
  rw [density_even, density_deriv_odd, density_second_deriv_even]
  simp [curvatureJet]

end ReciprocalXi
