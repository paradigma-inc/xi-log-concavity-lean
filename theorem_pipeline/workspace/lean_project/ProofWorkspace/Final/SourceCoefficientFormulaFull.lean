import ProofWorkspace.Final.RealTaylorBridgeFull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ReciprocalXi

def sourceTrigFactor (j : ℕ) (θ : ℝ) : ℝ :=
  (if j % 4 = 1 ∨ j % 4 = 2 then -1 else 1) *
    (if j % 2 = 0 then Real.cos θ else Real.sin θ)

def sourceCoefficientWeight (p : ℝ) (v : ℕ → ℝ) (j k : ℕ) : ℝ :=
  (1/(40*p))*v k*(if k=0 then 1/2 else 1)*((k:ℝ)/8000)^j/(j.factorial:ℝ)

theorem sourceCoefficientWeight_zero (p : ℝ) (v : ℕ → ℝ) (k : ℕ) :
    sourceCoefficientWeight p v 0 k =
      (1/(40*p))*v k*(if k=0 then 1/2 else 1) := by
  simp [sourceCoefficientWeight]

theorem sourceCoefficientWeight_succ (p : ℝ) (v : ℕ → ℝ) (j k : ℕ) :
    sourceCoefficientWeight p v (j+1) k =
      sourceCoefficientWeight p v j k*((k:ℝ)/8000)/(j+1:ℕ) := by
  simp only [sourceCoefficientWeight, Nat.factorial_succ, Nat.cast_mul,
    pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem complex_iteratedDeriv_cos_source (j : ℕ) (θ : ℝ) :
    iteratedDeriv j Complex.cos (θ:ℂ) = (sourceTrigFactor j θ:ℂ) := by
  have h4 : j%4=0 ∨ j%4=1 ∨ j%4=2 ∨ j%4=3 := by omega
  rcases h4 with h0 | h1 | h2 | h3
  · have he : j=2*(2*(j/4)) := by omega
    have he2 : j%2=0 := by omega
    conv_lhs => rw [he, Complex.iteratedDeriv_even_cos]
    simp [sourceTrigFactor, h0, he2, pow_mul, ← Complex.ofReal_cos]
  · have he : j=2*(2*(j/4))+1 := by omega
    have he2 : j%2=1 := by omega
    conv_lhs => rw [he, Complex.iteratedDeriv_odd_cos]
    simp [sourceTrigFactor, h1, he2, pow_add, pow_mul, ← Complex.ofReal_sin]
  · have he : j=2*(2*(j/4)+1) := by omega
    have he2 : j%2=0 := by omega
    conv_lhs => rw [he, Complex.iteratedDeriv_even_cos]
    simp [sourceTrigFactor, h2, he2, pow_add, pow_mul, ← Complex.ofReal_cos]
  · have he : j=2*(2*(j/4)+1)+1 := by omega
    have he2 : j%2=1 := by omega
    conv_lhs => rw [he, Complex.iteratedDeriv_odd_cos]
    simp [sourceTrigFactor, h3, he2, pow_add, pow_mul, ← Complex.ofReal_sin]

private theorem iteratedDeriv_affine_cos_zero (j : ℕ) (θ u : ℝ) :
    iteratedDeriv j (fun z : ℂ => Complex.cos ((θ:ℂ)+(u:ℂ)*z)) 0 =
      (u:ℂ)^j * (sourceTrigFactor j θ:ℂ) := by
  have hc : ContDiff ℂ j (fun z : ℂ => Complex.cos ((θ:ℂ)+z)) := by fun_prop
  rw [iteratedDeriv_comp_const_mul hc (u:ℂ), iteratedDeriv_comp_const_add]
  simp only [mul_zero, add_zero, complex_iteratedDeriv_cos_source]

private theorem normalizedSampledQuadrature_source_sum (c p : ℝ) (v : ℕ → ℝ) :
    normalizedSampledQuadrature c p v = fun z : ℂ =>
      ∑ k ∈ Finset.range 13601,
        ((1/(40*p)*v k*(if k=0 then 1/2 else 1):ℝ):ℂ) *
          Complex.cos (((k:ℝ)*c/40:ℝ)+(k/8000:ℝ)*z) := by
  funext z
  rw [show 13601=13600+1 from rfl, Finset.sum_range_succ']
  unfold normalizedSampledQuadrature sampledCosineQuadrature
  simp only [Complex.real_smul, Nat.cast_zero, zero_mul, zero_div, zero_add,
    Complex.ofReal_zero, Complex.cos_zero, mul_one, if_true,
    Nat.add_one_ne_zero, if_false, Nat.cast_add, Nat.cast_one]
  rw [mul_add, Finset.mul_sum]
  rw [add_comm]
  refine congrArg₂ (·+·) ?_ ?_
  · apply Finset.sum_congr rfl
    intro k hk
    have harg : ((c:ℂ)+(1/200:ℂ)*z)*((1/40:ℝ)*((k:ℝ)+1):ℝ) =
        (((k:ℝ)+1)*c/40:ℝ) + (((k:ℝ)+1)/8000:ℝ)*z := by
      push_cast
      ring
    rw [harg]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem sampledTaylorCoefficient_source_formula (c p : ℝ) (v : ℕ → ℝ) (j : ℕ) :
    sampledTaylorCoefficient c p v j =
      ((∑ k ∈ Finset.range 13601,
        sourceCoefficientWeight p v j k * sourceTrigFactor j ((k:ℝ)*c/40):ℝ):ℂ) := by
  have hd : ∀ k ∈ Finset.range 13601, ContDiffAt ℂ j
      (fun z : ℂ => ((1/(40*p)*v k*(if k=0 then 1/2 else 1):ℝ):ℂ) *
        Complex.cos (((k:ℝ)*c/40:ℝ)+(k/8000:ℝ)*z)) 0 := by
    intro k hk
    fun_prop
  unfold sampledTaylorCoefficient
  rw [normalizedSampledQuadrature_source_sum, iteratedDeriv_fun_sum hd]
  simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_affine_cos_zero]
  rw [Finset.mul_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold sourceCoefficientWeight
  push_cast
  ring

theorem realSampledTaylorPolynomial_source_coeff (c p : ℝ) (v : ℕ → ℝ)
    (j : ℕ) (hj : j ≤ 64) :
    (realSampledTaylorPolynomial c p v).coeff j =
      ∑ k ∈ Finset.range 13601,
        sourceCoefficientWeight p v j k * sourceTrigFactor j ((k:ℝ)*c/40) := by
  have hj' : j < 65 := by omega
  have he : (realSampledTaylorPolynomial c p v).coeff j =
      (sampledTaylorCoefficient c p v j).re := by
    simp [realSampledTaylorPolynomial, Polynomial.coeff_monomial, hj']
  rw [he, sampledTaylorCoefficient_source_formula]
  simp only [Complex.ofReal_re]

/-- The source's even/odd trigonometric selection followed by its mod-four sign. -/
def sourceCoefficientFormula (c p : ℝ) (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  let q := ∑ k ∈ Finset.range 13601, sourceCoefficientWeight p v j k *
    (if j%2=0 then Real.cos ((k:ℝ)*c/40) else Real.sin ((k:ℝ)*c/40))
  if j%4=1 ∨ j%4=2 then -q else q

theorem realSampledTaylorPolynomial_source_formula (c p : ℝ) (v : ℕ → ℝ)
    (j : ℕ) (hj : j ≤ 64) :
    (realSampledTaylorPolynomial c p v).coeff j = sourceCoefficientFormula c p v j := by
  rw [realSampledTaylorPolynomial_source_coeff c p v j hj]
  by_cases hj4 : j%4=1 ∨ j%4=2
  all_goals
    by_cases hj2 : j%2=0
    all_goals simp [sourceCoefficientFormula, sourceTrigFactor, hj4, hj2,
      Finset.sum_neg_distrib]

/-- The exact arithmetic recurrence used before source decimal rounding. -/
def sourceTrigRecurrence (θ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1,0)
  | k+1 =>
    let q := sourceTrigRecurrence θ k
    (q.1*Real.cos θ-q.2*Real.sin θ, q.2*Real.cos θ+q.1*Real.sin θ)

theorem sourceTrigRecurrence_eq (θ : ℝ) (k : ℕ) :
    sourceTrigRecurrence θ k = (Real.cos ((k:ℝ)*θ), Real.sin ((k:ℝ)*θ)) := by
  induction k with
  | zero => simp [sourceTrigRecurrence]
  | succ k ih =>
    simp only [sourceTrigRecurrence, ih, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul, Real.cos_add, Real.sin_add]

theorem sourceTrigRecurrence_panel (c : ℝ) (k : ℕ) :
    sourceTrigRecurrence (c/40) k =
      (Real.cos ((k:ℝ)*c/40), Real.sin ((k:ℝ)*c/40)) := by
  simpa [mul_div_assoc] using sourceTrigRecurrence_eq (c/40) k

end ReciprocalXi
