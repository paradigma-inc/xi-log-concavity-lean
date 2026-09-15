import ProofWorkspace.Final.FiniteTrapezoidBoundsFull
import ProofWorkspace.Final.XiFourierRealFull
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

theorem reciprocalTransform_zero : reciprocalTransform 0 = 1 := by
  rw [reciprocalTransform_eq_real_ratio]
  have h := ne_of_gt (xi_re_pos (1/2))
  norm_num only [add_zero, one_div] at *
  rw [div_self h]
  norm_num

theorem quadratureInput_pair (z : ℂ) (h x : ℝ) :
    quadratureInput z h x + quadratureInput z h (-x) =
      2 * reciprocalTransform (h*x) * Complex.cos (z*(h*x:ℝ)) := by
  have hep : -Complex.I*z*(h*x:ℝ) = -(z*(h*x:ℝ))*Complex.I := by ring
  have hen : -Complex.I*z*(h*(-x):ℝ) = (z*(h*x:ℝ))*Complex.I := by
    push_cast
    ring
  unfold quadratureInput
  rw [hep, hen, mul_neg, reciprocalTransform_even]
  calc
    _ = reciprocalTransform (h*x) *
        (Complex.exp ((z*(h*x:ℝ))*Complex.I) + Complex.exp (-(z*(h*x:ℝ))*Complex.I)) := by ring
    _ = reciprocalTransform (h*x) * (2 * Complex.cos (z*(h*x:ℝ))) := by
      rw [Complex.two_cos]
    _ = _ := by ring

theorem symmetric_quadrature_sum_eq_cosine (z : ℂ) (h : ℝ) (K : ℕ) :
    (∑ n ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), quadratureInput z h (n:ℝ)) =
      1 + 2 * ∑ j ∈ Finset.range K,
        reciprocalTransform (h*((j:ℝ)+1)) * Complex.cos (z*(h*((j:ℝ)+1):ℝ)) := by
  induction K with
  | zero => simp [quadratureInput, reciprocalTransform_zero]
  | succ K ih =>
    rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints, ih, Finset.sum_range_succ]
    have hp := quadratureInput_pair z h ((K:ℝ)+1)
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg]
    rw [hp]
    ring

theorem finiteTrapezoid_eq_cosine (z : ℂ) (h : ℝ) (K : ℕ) :
    finiteTrapezoid z h K =
      (h/(2*Real.pi)) • (1 + 2 * ∑ j ∈ Finset.range K,
        reciprocalTransform (h*((j:ℝ)+1)) * Complex.cos (z*(h*((j:ℝ)+1):ℝ))) := by
  unfold finiteTrapezoid
  rw [symmetric_quadrature_sum_eq_cosine]
end ReciprocalXi

