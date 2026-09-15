import ProofWorkspace.Final.SourcePanelCheckerFull

set_option autoImplicit false
open scoped BigOperators
namespace ReciprocalXi

def ratDensePanelCoeff (a : List ℤ) (j : ℕ) : ℚ :=
  if j < 65 then ratPanelCoefficient a j else 0
def ratDensePanelD1 (a : List ℤ) (j : ℕ) : ℚ :=
  ratDensePanelCoeff a (j+1)*(j+1)
def ratDensePanelD2 (a : List ℤ) (j : ℕ) : ℚ :=
  ratDensePanelD1 a (j+1)*(j+1)
def ratDensePanelCurvature (a : List ℤ) (j : ℕ) : ℚ :=
  (∑ x ∈ Finset.antidiagonal j, ratDensePanelD1 a x.1*ratDensePanelD1 a x.2) -
    ∑ x ∈ Finset.antidiagonal j, ratDensePanelCoeff a x.1*ratDensePanelD2 a x.2
def ratDenseNorm (f : ℕ → ℚ) (n : ℕ) : ℚ := ∑ j ∈ Finset.range n, |f j|

theorem ratPanelPolynomial_coeff_dense (a : List ℤ) (j : ℕ) :
    (ratPanelPolynomial a).coeff j = ratDensePanelCoeff a j := by
  simp [ratPanelPolynomial, ratDensePanelCoeff, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial]

theorem ratPanelDerivative_coeff_dense (a : List ℤ) (j : ℕ) :
    (ratPanelPolynomial a).derivative.coeff j = ratDensePanelD1 a j := by
  rw [Polynomial.coeff_derivative, ratPanelPolynomial_coeff_dense]
  rfl

theorem ratPanelSecondDerivative_coeff_dense (a : List ℤ) (j : ℕ) :
    (ratPanelPolynomial a).derivative.derivative.coeff j = ratDensePanelD2 a j := by
  rw [Polynomial.coeff_derivative, ratPanelDerivative_coeff_dense]
  rfl

theorem ratCurvaturePolynomial_coeff_dense (a : List ℤ) (j : ℕ) :
    (ratCurvaturePolynomial (ratPanelPolynomial a)).coeff j = ratDensePanelCurvature a j := by
  simp only [ratCurvaturePolynomial, pow_two, Polynomial.coeff_sub, Polynomial.coeff_mul,
    ratPanelPolynomial_coeff_dense, ratPanelDerivative_coeff_dense,
    ratPanelSecondDerivative_coeff_dense, ratDensePanelCurvature]

theorem ratDensePanelCoeff_zero (a : List ℤ) (j : ℕ) (hj : 65 ≤ j) :
    ratDensePanelCoeff a j = 0 := by
  simp [ratDensePanelCoeff, show ¬j<65 by omega]

theorem ratDensePanelD1_zero (a : List ℤ) (j : ℕ) (hj : 65 ≤ j) :
    ratDensePanelD1 a j = 0 := by
  simp [ratDensePanelD1, ratDensePanelCoeff_zero a (j+1) (by omega)]

theorem ratDensePanelD2_zero (a : List ℤ) (j : ℕ) (hj : 65 ≤ j) :
    ratDensePanelD2 a j = 0 := by
  simp [ratDensePanelD2, ratDensePanelD1_zero a (j+1) (by omega)]

theorem ratDensePanelCurvature_zero (a : List ℤ) (j : ℕ) (hj : 129 ≤ j) :
    ratDensePanelCurvature a j = 0 := by
  have ht : ∀ x ∈ Finset.antidiagonal j, 65 ≤ x.1 ∨ 65 ≤ x.2 := by
    intro x hx
    have hsum := Finset.mem_antidiagonal.mp hx
    omega
  have h1 : (∑ x ∈ Finset.antidiagonal j, ratDensePanelD1 a x.1*ratDensePanelD1 a x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rcases ht x hx with hl|hr
    · rw [ratDensePanelD1_zero a x.1 hl, zero_mul]
    · rw [ratDensePanelD1_zero a x.2 hr, mul_zero]
  have h2 : (∑ x ∈ Finset.antidiagonal j, ratDensePanelCoeff a x.1*ratDensePanelD2 a x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rcases ht x hx with hl|hr
    · rw [ratDensePanelCoeff_zero a x.1 hl, zero_mul]
    · rw [ratDensePanelD2_zero a x.2 hr, mul_zero]
  simp only [ratDensePanelCurvature, h1, h2, sub_self]

theorem ratCoefficientNorm_eq_dense (p : Polynomial ℚ) (n : ℕ)
    (hp : ∀ j, n ≤ j → p.coeff j = 0) :
    ratCoefficientNorm p = ratDenseNorm (fun j => p.coeff j) n := by
  unfold ratCoefficientNorm ratDenseNorm
  apply Finset.sum_subset
  · intro j hj
    apply Finset.mem_range.mpr
    by_contra h
    exact (Polynomial.mem_support_iff.mp hj) (hp j (by omega))
  · intro j _ hj
    have hz : p.coeff j = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hj
    simp [hz]

theorem ratPanelNorm_eq_dense (a : List ℤ) :
    ratCoefficientNorm (ratPanelPolynomial a) = ratDenseNorm (ratDensePanelCoeff a) 65 := by
  rw [ratCoefficientNorm_eq_dense _ 65]
  · simp only [ratPanelPolynomial_coeff_dense]
  · intro j hj
    rw [ratPanelPolynomial_coeff_dense, ratDensePanelCoeff_zero a j hj]

theorem ratPanelD1Norm_eq_dense (a : List ℤ) :
    ratCoefficientNorm (ratPanelPolynomial a).derivative = ratDenseNorm (ratDensePanelD1 a) 65 := by
  rw [ratCoefficientNorm_eq_dense _ 65]
  · simp only [ratPanelDerivative_coeff_dense]
  · intro j hj
    rw [ratPanelDerivative_coeff_dense, ratDensePanelD1_zero a j hj]

theorem ratPanelD2Norm_eq_dense (a : List ℤ) :
    ratCoefficientNorm (ratPanelPolynomial a).derivative.derivative = ratDenseNorm (ratDensePanelD2 a) 65 := by
  rw [ratCoefficientNorm_eq_dense _ 65]
  · simp only [ratPanelSecondDerivative_coeff_dense]
  · intro j hj
    rw [ratPanelSecondDerivative_coeff_dense, ratDensePanelD2_zero a j hj]

theorem ratPanelOffNorm_eq_dense (a : List ℤ) :
    ratCoefficientNorm ((ratCurvaturePolynomial (ratPanelPolynomial a)).erase 0) =
      ratDenseNorm (fun j => if j=0 then 0 else ratDensePanelCurvature a j) 129 := by
  rw [ratCoefficientNorm_eq_dense _ 129]
  · simp only [Polynomial.coeff_erase, ratCurvaturePolynomial_coeff_dense]
  · intro j hj
    simp [Polynomial.coeff_erase, ratCurvaturePolynomial_coeff_dense,
      ratDensePanelCurvature_zero a j hj]

def ratDensePanelPerturbation (a : List ℤ) : ℚ :=
  ratPanelD1*(2*ratDenseNorm (ratDensePanelD1 a) 65+ratPanelD1)+
    ratPanelD0*(ratDenseNorm (ratDensePanelD2 a) 65+ratPanelD2)+
    ratDenseNorm (ratDensePanelCoeff a) 65*ratPanelD2

def ratDensePanelErrorUpper (a : List ℤ) : ℚ :=
  ratSourcePanelJetUpper*(2*(ratDenseNorm (ratDensePanelD1 a) 65+ratPanelD1)+
    (ratDenseNorm (ratDensePanelCoeff a) 65+ratPanelD0)+
    (ratDenseNorm (ratDensePanelD2 a) 65+ratPanelD2))+2*ratSourcePanelJetUpper^2

def DenseSourcePanelChecks (i : Fin 318) (a : List ℤ) : Prop :=
  a.length=65 ∧
    ratRecordedConstantLower i ≤ ratDensePanelCurvature a 0-ratDensePanelPerturbation a ∧
    ratDenseNorm (fun j => if j=0 then 0 else ratDensePanelCurvature a j) 129+
      ratDensePanelPerturbation a ≤ ratRecordedOffUpper i ∧
    ratDensePanelErrorUpper a ≤ ratRecordedErrorUpper i

instance (i : Fin 318) (a : List ℤ) : Decidable (DenseSourcePanelChecks i a) := by
  unfold DenseSourcePanelChecks
  infer_instance

theorem sourcePanelChecks_iff_dense (i : Fin 318) (a : List ℤ) :
    SourcePanelChecks i a ↔ DenseSourcePanelChecks i a := by
  simp only [SourcePanelChecks, DenseSourcePanelChecks, ratCurvaturePolynomial_coeff_dense,
    ratPanelOffNorm_eq_dense, ratPanelCurvaturePerturbation, ratPanelCurvatureErrorUpper,
    ratDensePanelPerturbation, ratDensePanelErrorUpper, ratPanelNorm_eq_dense,
    ratPanelD1Norm_eq_dense, ratPanelD2Norm_eq_dense]

theorem sourcePanelCheck_iff_dense (i : Fin 318) (a : List ℤ) :
    sourcePanelCheck i a = true ↔ DenseSourcePanelChecks i a :=
  (sourcePanelCheck_iff i a).trans (sourcePanelChecks_iff_dense i a)

end ReciprocalXi

