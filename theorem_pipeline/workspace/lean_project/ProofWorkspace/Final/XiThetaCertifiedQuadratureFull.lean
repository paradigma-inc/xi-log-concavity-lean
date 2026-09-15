import ProofWorkspace.Final.XiThetaStoredQuadratureFull
import ProofWorkspace.Final.ThetaExpPanel0_0Full
import ProofWorkspace.Final.ThetaExpPanel0_1Full
import ProofWorkspace.Final.ThetaExpPanel0_2Full
import ProofWorkspace.Final.ThetaExpPanel0_3Full
import ProofWorkspace.Final.ThetaExpPanel0_4Full
import ProofWorkspace.Final.ThetaExpPanel0_5Full
import ProofWorkspace.Final.ThetaExpPanel0_6Full
import ProofWorkspace.Final.ThetaExpPanel0_7Full
import ProofWorkspace.Final.ThetaExpPanel1_0Full
import ProofWorkspace.Final.ThetaExpPanel1_1Full
import ProofWorkspace.Final.ThetaExpPanel1_2Full
import ProofWorkspace.Final.ThetaExpPanel1_3Full
import ProofWorkspace.Final.ThetaExpPanel1_4Full
import ProofWorkspace.Final.ThetaExpPanel1_5Full
import ProofWorkspace.Final.ThetaExpPanel1_6Full
import ProofWorkspace.Final.ThetaExpPanel1_7Full
import ProofWorkspace.Final.ThetaExpPanel2_0Full
import ProofWorkspace.Final.ThetaExpPanel2_1Full
import ProofWorkspace.Final.ThetaExpPanel2_2Full
import ProofWorkspace.Final.ThetaExpPanel2_3Full
import ProofWorkspace.Final.ThetaExpPanel2_4Full
import ProofWorkspace.Final.ThetaExpPanel2_5Full
import ProofWorkspace.Final.ThetaExpPanel2_6Full
import ProofWorkspace.Final.ThetaExpPanel2_7Full
import ProofWorkspace.Final.ThetaExpPanel3_0Full
import ProofWorkspace.Final.ThetaExpPanel3_1Full
import ProofWorkspace.Final.ThetaExpPanel3_2Full
import ProofWorkspace.Final.ThetaExpPanel3_3Full
import ProofWorkspace.Final.ThetaExpPanel3_4Full
import ProofWorkspace.Final.ThetaExpPanel3_5Full
import ProofWorkspace.Final.ThetaExpPanel3_6Full
import ProofWorkspace.Final.ThetaExpPanel3_7Full

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace ReciprocalXi

def theta48CertifiedPanel (j i : ℕ) : ℚ :=
  match j, i with
  | 0, 0 => thetaExpPanel0_0Value
  | 0, 1 => thetaExpPanel0_1Value
  | 0, 2 => thetaExpPanel0_2Value
  | 0, 3 => thetaExpPanel0_3Value
  | 0, 4 => thetaExpPanel0_4Value
  | 0, 5 => thetaExpPanel0_5Value
  | 0, 6 => thetaExpPanel0_6Value
  | 0, 7 => thetaExpPanel0_7Value
  | 1, 0 => thetaExpPanel1_0Value
  | 1, 1 => thetaExpPanel1_1Value
  | 1, 2 => thetaExpPanel1_2Value
  | 1, 3 => thetaExpPanel1_3Value
  | 1, 4 => thetaExpPanel1_4Value
  | 1, 5 => thetaExpPanel1_5Value
  | 1, 6 => thetaExpPanel1_6Value
  | 1, 7 => thetaExpPanel1_7Value
  | 2, 0 => thetaExpPanel2_0Value
  | 2, 1 => thetaExpPanel2_1Value
  | 2, 2 => thetaExpPanel2_2Value
  | 2, 3 => thetaExpPanel2_3Value
  | 2, 4 => thetaExpPanel2_4Value
  | 2, 5 => thetaExpPanel2_5Value
  | 2, 6 => thetaExpPanel2_6Value
  | 2, 7 => thetaExpPanel2_7Value
  | 3, 0 => thetaExpPanel3_0Value
  | 3, 1 => thetaExpPanel3_1Value
  | 3, 2 => thetaExpPanel3_2Value
  | 3, 3 => thetaExpPanel3_3Value
  | 3, 4 => thetaExpPanel3_4Value
  | 3, 5 => thetaExpPanel3_5Value
  | 3, 6 => thetaExpPanel3_6Value
  | 3, 7 => thetaExpPanel3_7Value
  | _, _ => 0

theorem theta48CertifiedPanel_error (j i : ℕ) (hj : j<4) (hi : i<8) :
    |theta48TaylorPanelValue (theta48PanelCenter j i) (theta48PanelHalfWidth j) 40-
      (theta48CertifiedPanel j i:ℝ)|≤320/(10:ℝ)^25 := by
  interval_cases j <;> interval_cases i
  · exact thetaExpPanel0_0_panel_error
  · exact thetaExpPanel0_1_panel_error
  · exact thetaExpPanel0_2_panel_error
  · exact thetaExpPanel0_3_panel_error
  · exact thetaExpPanel0_4_panel_error
  · exact thetaExpPanel0_5_panel_error
  · exact thetaExpPanel0_6_panel_error
  · exact thetaExpPanel0_7_panel_error
  · exact thetaExpPanel1_0_panel_error
  · exact thetaExpPanel1_1_panel_error
  · exact thetaExpPanel1_2_panel_error
  · exact thetaExpPanel1_3_panel_error
  · exact thetaExpPanel1_4_panel_error
  · exact thetaExpPanel1_5_panel_error
  · exact thetaExpPanel1_6_panel_error
  · exact thetaExpPanel1_7_panel_error
  · exact thetaExpPanel2_0_panel_error
  · exact thetaExpPanel2_1_panel_error
  · exact thetaExpPanel2_2_panel_error
  · exact thetaExpPanel2_3_panel_error
  · exact thetaExpPanel2_4_panel_error
  · exact thetaExpPanel2_5_panel_error
  · exact thetaExpPanel2_6_panel_error
  · exact thetaExpPanel2_7_panel_error
  · exact thetaExpPanel3_0_panel_error
  · exact thetaExpPanel3_1_panel_error
  · exact thetaExpPanel3_2_panel_error
  · exact thetaExpPanel3_3_panel_error
  · exact thetaExpPanel3_4_panel_error
  · exact thetaExpPanel3_5_panel_error
  · exact thetaExpPanel3_6_panel_error
  · exact thetaExpPanel3_7_panel_error

def theta48CertifiedQuadrature : ℚ :=
  ∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range 8, theta48CertifiedPanel j i

theorem theta48CertifiedQuadrature_cast : (theta48CertifiedQuadrature:ℝ)=
    theta48StoredQuadrature (fun j i ↦ (theta48CertifiedPanel j i:ℝ)) := by
  unfold theta48CertifiedQuadrature theta48StoredQuadrature
  push_cast <;> rfl

theorem theta48CertifiedQuadrature_eq : theta48CertifiedQuadrature=(21462636932460323474065343344803863097677816155793863769943038286330081:ℚ)/12367896891350000000000000000000000000000000000000000000000000000000000000 := by
  norm_num [theta48CertifiedQuadrature,theta48CertifiedPanel,Finset.sum_range_succ,
    thetaExpPanel0_0Value_eq,
    thetaExpPanel0_1Value_eq,
    thetaExpPanel0_2Value_eq,
    thetaExpPanel0_3Value_eq,
    thetaExpPanel0_4Value_eq,
    thetaExpPanel0_5Value_eq,
    thetaExpPanel0_6Value_eq,
    thetaExpPanel0_7Value_eq,
    thetaExpPanel1_0Value_eq,
    thetaExpPanel1_1Value_eq,
    thetaExpPanel1_2Value_eq,
    thetaExpPanel1_3Value_eq,
    thetaExpPanel1_4Value_eq,
    thetaExpPanel1_5Value_eq,
    thetaExpPanel1_6Value_eq,
    thetaExpPanel1_7Value_eq,
    thetaExpPanel2_0Value_eq,
    thetaExpPanel2_1Value_eq,
    thetaExpPanel2_2Value_eq,
    thetaExpPanel2_3Value_eq,
    thetaExpPanel2_4Value_eq,
    thetaExpPanel2_5Value_eq,
    thetaExpPanel2_6Value_eq,
    thetaExpPanel2_7Value_eq,
    thetaExpPanel3_0Value_eq,
    thetaExpPanel3_1Value_eq,
    thetaExpPanel3_2Value_eq,
    thetaExpPanel3_3Value_eq,
    thetaExpPanel3_4Value_eq,
    thetaExpPanel3_5Value_eq,
    thetaExpPanel3_6Value_eq,
    thetaExpPanel3_7Value_eq]

theorem F48_certifiedQuadrature_error :
    |(F (48:ℂ)).re-(1-(2305/4:ℝ)*(theta48CertifiedQuadrature:ℝ))/8|≤3/(10:ℝ)^16 := by
  rw [theta48CertifiedQuadrature_cast]
  exact F48_storedQuadrature_error _ (fun j hj i hi ↦ theta48CertifiedPanel_error j i hj hi)

theorem F48_source_enclosure :
    529169286414/(10:ℝ)^18<(F (48:ℂ)).re ∧
    (F (48:ℂ)).re<529196177592/(10:ℝ)^18 := by
  have he := F48_certifiedQuadrature_error
  rw [theta48CertifiedQuadrature_eq] at he
  norm_num at he
  obtain ⟨hl,hu⟩ := abs_le.mp he
  constructor <;> linarith

theorem F48_source_lower : 529169286414/(10:ℝ)^18≤(F (48:ℂ)).re :=
  F48_source_enclosure.1.le

end ReciprocalXi
