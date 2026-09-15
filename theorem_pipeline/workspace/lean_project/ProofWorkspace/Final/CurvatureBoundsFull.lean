import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic curvature bounds used by the reciprocal-Xi proof

This file formalizes an algebraic component of the reviewed argument, not the
reciprocal-Xi theorem itself. Analytic remainder estimates and the connection
between the actual density and its approximations are explicit hypotheses.
-/

namespace ReciprocalXi

/-- The curvature numerator at a function's value, first derivative and second
derivative. For a positive twice differentiable function, the second logarithmic
derivative is the negative of this expression divided by the square of its value. -/
def curvatureJet (v v1 v2 : ℝ) : ℝ := v1 ^ 2 - v * v2

/-- Exact expansion of the curvature numerator under a three-component error. -/
theorem curvatureJet_perturbation_identity (p0 p1 p2 r0 r1 r2 : ℝ) :
    curvatureJet (p0 + r0) (p1 + r1) (p2 + r2) - curvatureJet p0 p1 p2 =
      (2 * p1 * r1 + r1 ^ 2) - (p0 * r2 + r0 * p2 + r0 * r2) := by
  unfold curvatureJet
  ring

/-- The uniform error bound used in the compact-interval certificate. All value
and derivative bounds occur as hypotheses; this does not infer derivatives from
sampled function values. -/
theorem curvatureJet_perturbation_bound
    (p0 p1 p2 r0 r1 r2 e N0 N1 N2 : ℝ)
    (he : 0 ≤ e) (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (hp0 : |p0| ≤ N0) (hp1 : |p1| ≤ N1) (hp2 : |p2| ≤ N2)
    (hr0 : |r0| ≤ e) (hr1 : |r1| ≤ e) (hr2 : |r2| ≤ e) :
    |curvatureJet (p0 + r0) (p1 + r1) (p2 + r2) - curvatureJet p0 p1 p2| ≤
      e * (2 * N1 + N0 + N2) + 2 * e ^ 2 := by
  have h01 : |p0 * r2| ≤ N0 * e := by
    rw [abs_mul]
    exact mul_le_mul hp0 hr2 (abs_nonneg _) hN0
  have h02 : |r0 * p2| ≤ e * N2 := by
    rw [abs_mul]
    calc
      |r0| * |p2| ≤ |r0| * N2 := mul_le_mul_of_nonneg_left hp2 (abs_nonneg _)
      _ ≤ e * N2 := mul_le_mul_of_nonneg_right hr0 hN2
  have h03 : |r0 * r2| ≤ e ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hr0 hr2 (abs_nonneg _) he
  have h11 : |2 * p1 * r1| ≤ 2 * N1 * e := by
    calc
      |2 * p1 * r1| = 2 * |p1| * |r1| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * N1 * e := by gcongr
  have h12 : |r1 ^ 2| ≤ e ^ 2 := by
    rw [abs_pow]
    gcongr
  have hleft : |2 * p1 * r1 + r1 ^ 2| ≤ 2 * N1 * e + e ^ 2 :=
    (abs_add_le _ _).trans (add_le_add h11 h12)
  have hright : |p0 * r2 + r0 * p2 + r0 * r2| ≤ N0 * e + e * N2 + e ^ 2 :=
    (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add h01 h02)) h03)
  rw [curvatureJet_perturbation_identity]
  calc
    |(2 * p1 * r1 + r1 ^ 2) - (p0 * r2 + r0 * p2 + r0 * r2)| ≤
        |2 * p1 * r1 + r1 ^ 2| + |p0 * r2 + r0 * p2 + r0 * r2| :=
      abs_sub _ _
    _ ≤ (2 * N1 * e + e ^ 2) + (N0 * e + e * N2 + e ^ 2) :=
      add_le_add hleft hright
    _ = e * (2 * N1 + N0 + N2) + 2 * e ^ 2 := by ring

/-- A strictly positive certified margin survives the explicitly bounded error. -/
theorem curvatureJet_positive_of_margin
    (p0 p1 p2 r0 r1 r2 e N0 N1 N2 : ℝ)
    (he : 0 ≤ e) (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (hp0 : |p0| ≤ N0) (hp1 : |p1| ≤ N1) (hp2 : |p2| ≤ N2)
    (hr0 : |r0| ≤ e) (hr1 : |r1| ≤ e) (hr2 : |r2| ≤ e)
    (hmargin : e * (2 * N1 + N0 + N2) + 2 * e ^ 2 < curvatureJet p0 p1 p2) :
    0 < curvatureJet (p0 + r0) (p1 + r1) (p2 + r2) := by
  have hbound := curvatureJet_perturbation_bound p0 p1 p2 r0 r1 r2 e N0 N1 N2
    he hN0 hN1 hN2 hp0 hp1 hp2 hr0 hr1 hr2
  have hlower := (abs_le.mp hbound).1
  linarith

/-- Exact cancellation of the two square terms in the two-exponential model.
The variables `s` and `t` may later be instantiated with exponential values. -/
theorem twoExponentialJet_curvature (A B a b s t : ℝ) :
    curvatureJet (A * s - B * t) (-a * A * s + b * B * t)
      (a ^ 2 * A * s - b ^ 2 * B * t) = A * B * (b - a) ^ 2 * s * t := by
  unfold curvatureJet
  ring

/-- The two-exponential curvature is strictly positive when its coefficients
and exponential factors are positive and its rates are distinct. -/
theorem twoExponentialJet_curvature_pos (A B a b s t : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hst : 0 < s) (htt : 0 < t) (hab : a ≠ b) :
    0 < curvatureJet (A * s - B * t) (-a * A * s + b * B * t)
      (a ^ 2 * A * s - b ^ 2 * B * t) := by
  rw [twoExponentialJet_curvature]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hsq : 0 < (b - a) ^ 2 := sq_pos_of_ne_zero hba
  positivity

/-- The leading two-real-pole approximation, as an actual real function. -/
noncomputable def twoExponential (A B a b : ℝ) (x : ℝ) : ℝ :=
  A * Real.exp (-a * x) - B * Real.exp (-b * x)

/-- Its first derivative formula. -/
theorem hasDerivAt_twoExponential (A B a b x : ℝ) :
    HasDerivAt (twoExponential A B a b)
      (-a * A * Real.exp (-a * x) + b * B * Real.exp (-b * x)) x := by
  convert
    (((hasDerivAt_id x).const_mul (-a)).exp.const_mul A).sub
      (((hasDerivAt_id x).const_mul (-b)).exp.const_mul B) using 1
  simp only [id_eq]
  ring

/-- Its second derivative formula. -/
theorem hasDerivAt_twoExponential_first (A B a b x : ℝ) :
    HasDerivAt
      (fun y : ℝ => -a * A * Real.exp (-a * y) + b * B * Real.exp (-b * y))
      (a ^ 2 * A * Real.exp (-a * x) - b ^ 2 * B * Real.exp (-b * x)) x := by
  convert
    (((hasDerivAt_id x).const_mul (-a)).exp.const_mul (-a * A)).add
      (((hasDerivAt_id x).const_mul (-b)).exp.const_mul (b * B)) using 1
  simp only [id_eq]
  ring

/-- The curvature identity for the actual two-exponential function, expressed
using its proved derivative formulas. -/
theorem twoExponential_curvature (A B a b x : ℝ) :
    curvatureJet (twoExponential A B a b x)
      (deriv (twoExponential A B a b) x)
      (deriv (deriv (twoExponential A B a b)) x) =
      A * B * (b - a) ^ 2 * Real.exp (-(a + b) * x) := by
  have hfirst : deriv (twoExponential A B a b) =
      fun y : ℝ => -a * A * Real.exp (-a * y) + b * B * Real.exp (-b * y) := by
    funext y
    exact (hasDerivAt_twoExponential A B a b y).deriv
  rw [hfirst, (hasDerivAt_twoExponential_first A B a b x).deriv]
  unfold twoExponential
  rw [twoExponentialJet_curvature]
  rw [mul_assoc (A * B * (b - a) ^ 2), ← Real.exp_add]
  congr 2
  ring

/-- Strict positive curvature of the actual two-exponential function. -/
theorem twoExponential_curvature_pos (A B a b x : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hab : a ≠ b) :
    0 < curvatureJet (twoExponential A B a b x)
      (deriv (twoExponential A B a b) x)
      (deriv (deriv (twoExponential A B a b)) x) := by
  rw [twoExponential_curvature]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hsq : 0 < (b - a) ^ 2 := sq_pos_of_ne_zero hba
  positivity

end ReciprocalXi
