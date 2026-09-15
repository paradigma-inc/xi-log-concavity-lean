import ProofWorkspace.Final.DensityTaylorErrorFull
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

private theorem iteratedDeriv_restriction_re (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => (f (t:ℂ)).re) x =
      (iteratedDeriv n f (x:ℂ)).re := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have he : iteratedDeriv n (fun t : ℝ => (f (t:ℂ)).re) =
        fun t : ℝ => (iteratedDeriv n f (t:ℂ)).re := funext ih
    rw [he]
    have hn : Differentiable ℂ (iteratedDeriv n f) :=
      (hf.contDiff : ContDiff ℂ (n+1) f).differentiable_iteratedDeriv' n
    exact (hn (x:ℂ)).hasDerivAt.real_of_complex.deriv

/-- The degree-64 real polynomial formed from the actual complex Taylor coefficients. -/
def realSampledTaylorPolynomial (c p : ℝ) (v : ℕ → ℝ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range 65,
    Polynomial.monomial n (sampledTaylorCoefficient c p v n).re

theorem realSampledTaylorPolynomial_eval (c p x : ℝ) (v : ℕ → ℝ) :
    (realSampledTaylorPolynomial c p v).eval x =
      (sampledTaylorPolynomial64 c p v (x:ℂ)).re := by
  simp [realSampledTaylorPolynomial, sampledTaylorPolynomial64,
    Polynomial.eval_finset_sum, Complex.mul_re, ← Complex.ofReal_pow]

private theorem polynomial_iteratedDeriv_eval (p : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => p.eval x) =
      fun x : ℝ => (Polynomial.derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext x
    exact ((Polynomial.derivative^[n] p).hasDerivAt x).deriv

theorem realSampledTaylorPolynomial_iterated_derivative_eval
    (c p x : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    (Polynomial.derivative^[n] (realSampledTaylorPolynomial c p v)).eval x =
      (iteratedDeriv n (sampledTaylorPolynomial64 c p v) (x:ℂ)).re := by
  rw [← congrFun (polynomial_iteratedDeriv_eval (realSampledTaylorPolynomial c p v) n) x]
  have he : (fun x : ℝ => (realSampledTaylorPolynomial c p v).eval x) =
      fun x : ℝ => (sampledTaylorPolynomial64 c p v (x:ℂ)).re := by
    funext x
    exact realSampledTaylorPolynomial_eval c p x v
  rw [he]
  exact iteratedDeriv_restriction_re _
    (differentiable_sampledTaylorPolynomial64 c p v) n x

theorem realSampledTaylorPolynomial_derivative_eval
    (c p x : ℝ) (v : ℕ → ℝ) :
    (realSampledTaylorPolynomial c p v).derivative.eval x =
      (iteratedDeriv 1 (sampledTaylorPolynomial64 c p v) (x:ℂ)).re := by
  simpa using realSampledTaylorPolynomial_iterated_derivative_eval c p x v 1

theorem realSampledTaylorPolynomial_second_derivative_eval
    (c p x : ℝ) (v : ℕ → ℝ) :
    (realSampledTaylorPolynomial c p v).derivative.derivative.eval x =
      (iteratedDeriv 2 (sampledTaylorPolynomial64 c p v) (x:ℂ)).re := by
  simpa [Function.iterate_succ_apply'] using
    realSampledTaylorPolynomial_iterated_derivative_eval c p x v 2

theorem normalizedComplexDensity_ofReal_re (c x : ℝ) :
    (normalizedComplexDensity c (x:ℂ)).re = density (c+(1/200:ℝ)*x) := by
  have he : (c:ℂ)+(1/200:ℂ)*(x:ℂ) = ((c+(1/200:ℝ)*x:ℝ):ℂ) := by
    push_cast
    rfl
  unfold normalizedComplexDensity
  rw [he, complexDensity_ofReal]
  rfl

private theorem deriv_normalized_real_density (c : ℝ) :
    deriv (fun x : ℝ => density (c+(1/200:ℝ)*x)) =
      fun x : ℝ => (1/200:ℝ)*deriv density (c+(1/200:ℝ)*x) := by
  funext x
  have h := (differentiable_density (c+(1/200:ℝ)*x)).hasDerivAt.comp x
    (((hasDerivAt_id x).const_mul (1/200:ℝ)).const_add c)
  simpa [mul_comm] using h.deriv

theorem normalizedComplexDensity_deriv_re (c x : ℝ) :
    (iteratedDeriv 1 (normalizedComplexDensity c) (x:ℂ)).re =
      (1/200:ℝ)*deriv density (c+(1/200:ℝ)*x) := by
  rw [← iteratedDeriv_restriction_re _ (differentiable_normalizedComplexDensity c)]
  have he : (fun x : ℝ => (normalizedComplexDensity c (x:ℂ)).re) =
      fun x : ℝ => density (c+(1/200:ℝ)*x) := by
    funext x
    exact normalizedComplexDensity_ofReal_re c x
  rw [he]
  simpa using congrFun (deriv_normalized_real_density c) x

theorem normalizedComplexDensity_second_deriv_re (c x : ℝ) :
    (iteratedDeriv 2 (normalizedComplexDensity c) (x:ℂ)).re =
      (1/200:ℝ)^2*deriv (deriv density) (c+(1/200:ℝ)*x) := by
  rw [← iteratedDeriv_restriction_re _ (differentiable_normalizedComplexDensity c)]
  have he : (fun x : ℝ => (normalizedComplexDensity c (x:ℂ)).re) =
      fun x : ℝ => density (c+(1/200:ℝ)*x) := by
    funext x
    exact normalizedComplexDensity_ofReal_re c x
  rw [he]
  simp only [show (2:ℕ)=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_normalized_real_density]
  have h := ((differentiable_deriv_density (c+(1/200:ℝ)*x)).hasDerivAt.comp x
    (((hasDerivAt_id x).const_mul (1/200:ℝ)).const_add c)).const_mul (1/200:ℝ)
  convert h.deriv using 1
  ring

end ReciprocalXi
