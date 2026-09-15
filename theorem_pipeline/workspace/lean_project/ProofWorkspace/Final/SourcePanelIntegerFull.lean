import ProofWorkspace.Final.SourcePanelDenseFull

set_option autoImplicit false
open scoped BigOperators
namespace ReciprocalXi

def intPanelCoeff (a : List ℤ) (j : ℕ) : ℤ :=
  if j < 65 then (a[j]?).getD 0 else 0
def intPanelD1 (a : List ℤ) (j : ℕ) : ℤ := intPanelCoeff a (j+1)*(j+1)
def intPanelD2 (a : List ℤ) (j : ℕ) : ℤ := intPanelD1 a (j+1)*(j+1)
def intPanelCurvature (a : List ℤ) (j : ℕ) : ℤ :=
  (∑ x ∈ Finset.antidiagonal j, intPanelD1 a x.1*intPanelD1 a x.2) -
    ∑ x ∈ Finset.antidiagonal j, intPanelCoeff a x.1*intPanelD2 a x.2
def intPanelNorm (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, |f j|

theorem ratDensePanelCoeff_eq_int (a : List ℤ) (j : ℕ) :
    ratDensePanelCoeff a j = (intPanelCoeff a j:ℚ)/sourceCoefficientScale := by
  unfold ratDensePanelCoeff intPanelCoeff
  split_ifs <;> simp [ratPanelCoefficient, sourceGridDecode]

theorem ratDensePanelD1_eq_int (a : List ℤ) (j : ℕ) :
    ratDensePanelD1 a j = (intPanelD1 a j:ℚ)/sourceCoefficientScale := by
  unfold ratDensePanelD1 intPanelD1
  rw [ratDensePanelCoeff_eq_int]
  push_cast
  ring

theorem ratDensePanelD2_eq_int (a : List ℤ) (j : ℕ) :
    ratDensePanelD2 a j = (intPanelD2 a j:ℚ)/sourceCoefficientScale := by
  unfold ratDensePanelD2 intPanelD2
  rw [ratDensePanelD1_eq_int]
  push_cast
  ring

theorem ratDensePanelCurvature_eq_int (a : List ℤ) (j : ℕ) :
    ratDensePanelCurvature a j =
      (intPanelCurvature a j:ℚ)/(sourceCoefficientScale:ℚ)^2 := by
  unfold ratDensePanelCurvature intPanelCurvature
  simp_rw [ratDensePanelCoeff_eq_int, ratDensePanelD1_eq_int, ratDensePanelD2_eq_int,
    div_mul_div_comm, ←Finset.sum_div]
  push_cast
  ring

theorem ratDenseNorm_eq_int (f : ℕ → ℤ) (n : ℕ) (B : ℚ) (hB : 0 < B) :
    ratDenseNorm (fun j => (f j:ℚ)/B) n = (intPanelNorm f n:ℚ)/B := by
  unfold ratDenseNorm intPanelNorm
  simp_rw [abs_div, abs_of_pos hB]
  rw [←Finset.sum_div]
  push_cast
  rfl

def ratIntPanelNorm (a : List ℤ) : ℚ :=
  (intPanelNorm (intPanelCoeff a) 65:ℚ)/sourceCoefficientScale
def ratIntPanelD1Norm (a : List ℤ) : ℚ :=
  (intPanelNorm (intPanelD1 a) 65:ℚ)/sourceCoefficientScale
def ratIntPanelD2Norm (a : List ℤ) : ℚ :=
  (intPanelNorm (intPanelD2 a) 65:ℚ)/sourceCoefficientScale
def ratIntPanelOffNorm (a : List ℤ) : ℚ :=
  (intPanelNorm (fun j => if j=0 then 0 else intPanelCurvature a j) 129:ℚ)/
    (sourceCoefficientScale:ℚ)^2

private theorem sourceCoefficientScale_rat_pos : (0:ℚ) < sourceCoefficientScale := by
  norm_num [sourceCoefficientScale]

theorem ratDenseNorm_panel_eq_int (a : List ℤ) :
    ratDenseNorm (ratDensePanelCoeff a) 65 = ratIntPanelNorm a := by
  unfold ratDenseNorm
  simp_rw [ratDensePanelCoeff_eq_int]
  exact ratDenseNorm_eq_int _ _ _ sourceCoefficientScale_rat_pos

theorem ratDenseNorm_d1_eq_int (a : List ℤ) :
    ratDenseNorm (ratDensePanelD1 a) 65 = ratIntPanelD1Norm a := by
  unfold ratDenseNorm
  simp_rw [ratDensePanelD1_eq_int]
  exact ratDenseNorm_eq_int _ _ _ sourceCoefficientScale_rat_pos

theorem ratDenseNorm_d2_eq_int (a : List ℤ) :
    ratDenseNorm (ratDensePanelD2 a) 65 = ratIntPanelD2Norm a := by
  unfold ratDenseNorm
  simp_rw [ratDensePanelD2_eq_int]
  exact ratDenseNorm_eq_int _ _ _ sourceCoefficientScale_rat_pos

theorem ratDenseNorm_off_eq_int (a : List ℤ) :
    ratDenseNorm (fun j => if j=0 then 0 else ratDensePanelCurvature a j) 129 =
      ratIntPanelOffNorm a := by
  have hf : (fun j => if j=0 then 0 else ratDensePanelCurvature a j) =
      (fun j => ((if j=0 then 0 else intPanelCurvature a j:ℤ):ℚ)/
        (sourceCoefficientScale:ℚ)^2) := by
    funext j
    by_cases hj : j=0 <;> simp [hj, ratDensePanelCurvature_eq_int]
  rw [hf]
  exact ratDenseNorm_eq_int _ _ _ (sq_pos_of_pos sourceCoefficientScale_rat_pos)

def ratIntPanelPerturbation (a : List ℤ) : ℚ :=
  ratPanelD1*(2*ratIntPanelD1Norm a+ratPanelD1)+
    ratPanelD0*(ratIntPanelD2Norm a+ratPanelD2)+ratIntPanelNorm a*ratPanelD2

def ratIntPanelErrorUpper (a : List ℤ) : ℚ :=
  ratSourcePanelJetUpper*(2*(ratIntPanelD1Norm a+ratPanelD1)+
    (ratIntPanelNorm a+ratPanelD0)+(ratIntPanelD2Norm a+ratPanelD2))+
    2*ratSourcePanelJetUpper^2

def IntegerSourcePanelChecks (i : Fin 318) (a : List ℤ) : Prop :=
  a.length=65 ∧
    ratRecordedConstantLower i ≤
      (intPanelCurvature a 0:ℚ)/(sourceCoefficientScale:ℚ)^2-ratIntPanelPerturbation a ∧
    ratIntPanelOffNorm a+ratIntPanelPerturbation a ≤ ratRecordedOffUpper i ∧
    ratIntPanelErrorUpper a ≤ ratRecordedErrorUpper i

instance (i : Fin 318) (a : List ℤ) : Decidable (IntegerSourcePanelChecks i a) := by
  unfold IntegerSourcePanelChecks
  infer_instance

theorem sourcePanelCheck_iff_integer (i : Fin 318) (a : List ℤ) :
    sourcePanelCheck i a = true ↔ IntegerSourcePanelChecks i a := by
  rw [sourcePanelCheck_iff_dense]
  unfold DenseSourcePanelChecks
  rw [ratDenseNorm_off_eq_int]
  simp only [IntegerSourcePanelChecks, ratDensePanelCurvature_eq_int,
    ratDensePanelPerturbation, ratIntPanelPerturbation, ratDensePanelErrorUpper,
    ratIntPanelErrorUpper, ratDenseNorm_panel_eq_int, ratDenseNorm_d1_eq_int,
    ratDenseNorm_d2_eq_int]

end ReciprocalXi

