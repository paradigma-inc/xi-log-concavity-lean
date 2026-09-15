import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroPanelP1J0I0Full
import ProofWorkspace.Final.LowZeroPanelP1J0I1Full
import ProofWorkspace.Final.LowZeroPanelP1J0I2Full
import ProofWorkspace.Final.LowZeroPanelP1J0I3Full
import ProofWorkspace.Final.LowZeroPanelP1J0I4Full
import ProofWorkspace.Final.LowZeroPanelP1J0I5Full
import ProofWorkspace.Final.LowZeroPanelP1J0I6Full
import ProofWorkspace.Final.LowZeroPanelP1J0I7Full
import ProofWorkspace.Final.LowZeroPanelP1J1I0Full
import ProofWorkspace.Final.LowZeroPanelP1J1I1Full
import ProofWorkspace.Final.LowZeroPanelP1J1I2Full
import ProofWorkspace.Final.LowZeroPanelP1J1I3Full
import ProofWorkspace.Final.LowZeroPanelP1J1I4Full
import ProofWorkspace.Final.LowZeroPanelP1J1I5Full
import ProofWorkspace.Final.LowZeroPanelP1J1I6Full
import ProofWorkspace.Final.LowZeroPanelP1J1I7Full
import ProofWorkspace.Final.LowZeroPanelP1J2I0Full
import ProofWorkspace.Final.LowZeroPanelP1J2I1Full
import ProofWorkspace.Final.LowZeroPanelP1J2I2Full
import ProofWorkspace.Final.LowZeroPanelP1J2I3Full
import ProofWorkspace.Final.LowZeroPanelP1J2I4Full
import ProofWorkspace.Final.LowZeroPanelP1J2I5Full
import ProofWorkspace.Final.LowZeroPanelP1J2I6Full
import ProofWorkspace.Final.LowZeroPanelP1J2I7Full
import ProofWorkspace.Final.LowZeroPanelP1J3I0Full
import ProofWorkspace.Final.LowZeroPanelP1J3I1Full
import ProofWorkspace.Final.LowZeroPanelP1J3I2Full
import ProofWorkspace.Final.LowZeroPanelP1J3I3Full
import ProofWorkspace.Final.LowZeroPanelP1J3I4Full
import ProofWorkspace.Final.LowZeroPanelP1J3I5Full
import ProofWorkspace.Final.LowZeroPanelP1J3I6Full
import ProofWorkspace.Final.LowZeroPanelP1J3I7Full
import ProofWorkspace.Final.LowZeroPanelP1J4I0Full
import ProofWorkspace.Final.LowZeroPanelP1J4I1Full
import ProofWorkspace.Final.LowZeroPanelP1J4I2Full
import ProofWorkspace.Final.LowZeroPanelP1J4I3Full
import ProofWorkspace.Final.LowZeroPanelP1J4I4Full
import ProofWorkspace.Final.LowZeroPanelP1J4I5Full
import ProofWorkspace.Final.LowZeroPanelP1J4I6Full
import ProofWorkspace.Final.LowZeroPanelP1J4I7Full

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace ReciprocalXi

def lowZeroEndpointP1Point : ℚ := lowZeroSeedP1J0I0K1Point

def lowZeroEndpointP1Panel (j i : ℕ) : ℚ :=
  match j, i with
  | 0, 0 => lowZeroPanelP1J0I0Value
  | 0, 1 => lowZeroPanelP1J0I1Value
  | 0, 2 => lowZeroPanelP1J0I2Value
  | 0, 3 => lowZeroPanelP1J0I3Value
  | 0, 4 => lowZeroPanelP1J0I4Value
  | 0, 5 => lowZeroPanelP1J0I5Value
  | 0, 6 => lowZeroPanelP1J0I6Value
  | 0, 7 => lowZeroPanelP1J0I7Value
  | 1, 0 => lowZeroPanelP1J1I0Value
  | 1, 1 => lowZeroPanelP1J1I1Value
  | 1, 2 => lowZeroPanelP1J1I2Value
  | 1, 3 => lowZeroPanelP1J1I3Value
  | 1, 4 => lowZeroPanelP1J1I4Value
  | 1, 5 => lowZeroPanelP1J1I5Value
  | 1, 6 => lowZeroPanelP1J1I6Value
  | 1, 7 => lowZeroPanelP1J1I7Value
  | 2, 0 => lowZeroPanelP1J2I0Value
  | 2, 1 => lowZeroPanelP1J2I1Value
  | 2, 2 => lowZeroPanelP1J2I2Value
  | 2, 3 => lowZeroPanelP1J2I3Value
  | 2, 4 => lowZeroPanelP1J2I4Value
  | 2, 5 => lowZeroPanelP1J2I5Value
  | 2, 6 => lowZeroPanelP1J2I6Value
  | 2, 7 => lowZeroPanelP1J2I7Value
  | 3, 0 => lowZeroPanelP1J3I0Value
  | 3, 1 => lowZeroPanelP1J3I1Value
  | 3, 2 => lowZeroPanelP1J3I2Value
  | 3, 3 => lowZeroPanelP1J3I3Value
  | 3, 4 => lowZeroPanelP1J3I4Value
  | 3, 5 => lowZeroPanelP1J3I5Value
  | 3, 6 => lowZeroPanelP1J3I6Value
  | 3, 7 => lowZeroPanelP1J3I7Value
  | 4, 0 => lowZeroPanelP1J4I0Value
  | 4, 1 => lowZeroPanelP1J4I1Value
  | 4, 2 => lowZeroPanelP1J4I2Value
  | 4, 3 => lowZeroPanelP1J4I3Value
  | 4, 4 => lowZeroPanelP1J4I4Value
  | 4, 5 => lowZeroPanelP1J4I5Value
  | 4, 6 => lowZeroPanelP1J4I6Value
  | 4, 7 => lowZeroPanelP1J4I7Value
  | _, _ => 0

theorem lowZeroEndpointP1_panel_error (j i : ℕ) (hj : j<5) (hi : i<8) :
    |lowZeroThetaTaylorPanelValue lowZeroEndpointP1Point (theta48PanelCenter j i)
      (theta48PanelHalfWidth j) 80-(lowZeroEndpointP1Panel j i:ℝ)|≤1600/(10:ℝ)^50 := by
  interval_cases j <;> interval_cases i
  · exact lowZeroPanelP1J0I0_panel_error
  · exact lowZeroPanelP1J0I1_panel_error
  · exact lowZeroPanelP1J0I2_panel_error
  · exact lowZeroPanelP1J0I3_panel_error
  · exact lowZeroPanelP1J0I4_panel_error
  · exact lowZeroPanelP1J0I5_panel_error
  · exact lowZeroPanelP1J0I6_panel_error
  · exact lowZeroPanelP1J0I7_panel_error
  · exact lowZeroPanelP1J1I0_panel_error
  · exact lowZeroPanelP1J1I1_panel_error
  · exact lowZeroPanelP1J1I2_panel_error
  · exact lowZeroPanelP1J1I3_panel_error
  · exact lowZeroPanelP1J1I4_panel_error
  · exact lowZeroPanelP1J1I5_panel_error
  · exact lowZeroPanelP1J1I6_panel_error
  · exact lowZeroPanelP1J1I7_panel_error
  · exact lowZeroPanelP1J2I0_panel_error
  · exact lowZeroPanelP1J2I1_panel_error
  · exact lowZeroPanelP1J2I2_panel_error
  · exact lowZeroPanelP1J2I3_panel_error
  · exact lowZeroPanelP1J2I4_panel_error
  · exact lowZeroPanelP1J2I5_panel_error
  · exact lowZeroPanelP1J2I6_panel_error
  · exact lowZeroPanelP1J2I7_panel_error
  · exact lowZeroPanelP1J3I0_panel_error
  · exact lowZeroPanelP1J3I1_panel_error
  · exact lowZeroPanelP1J3I2_panel_error
  · exact lowZeroPanelP1J3I3_panel_error
  · exact lowZeroPanelP1J3I4_panel_error
  · exact lowZeroPanelP1J3I5_panel_error
  · exact lowZeroPanelP1J3I6_panel_error
  · exact lowZeroPanelP1J3I7_panel_error
  · exact lowZeroPanelP1J4I0_panel_error
  · exact lowZeroPanelP1J4I1_panel_error
  · exact lowZeroPanelP1J4I2_panel_error
  · exact lowZeroPanelP1J4I3_panel_error
  · exact lowZeroPanelP1J4I4_panel_error
  · exact lowZeroPanelP1J4I5_panel_error
  · exact lowZeroPanelP1J4I6_panel_error
  · exact lowZeroPanelP1J4I7_panel_error

def lowZeroEndpointP1Quadrature : ℚ :=
  ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 8, lowZeroEndpointP1Panel j i

theorem lowZeroEndpointP1_quadrature_cast : (lowZeroEndpointP1Quadrature:ℝ)=
    lowZeroStoredQuadrature (fun j i ↦ (lowZeroEndpointP1Panel j i:ℝ)) := by
  unfold lowZeroEndpointP1Quadrature lowZeroStoredQuadrature
  push_cast <;> rfl

theorem lowZeroEndpointP1_quadrature_eq : lowZeroEndpointP1Quadrature=(536165675427457125958071416578970415684614237471876324402009141650549131952723007184879302764954484274891794886987270394198028289040647995790077410597305847712640116138687334441891560544823:ℚ)/107254825578022430263302818471000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  norm_num [lowZeroEndpointP1Quadrature,lowZeroEndpointP1Panel,Finset.sum_range_succ,
    lowZeroPanelP1J0I0Value_eq,
    lowZeroPanelP1J0I1Value_eq,
    lowZeroPanelP1J0I2Value_eq,
    lowZeroPanelP1J0I3Value_eq,
    lowZeroPanelP1J0I4Value_eq,
    lowZeroPanelP1J0I5Value_eq,
    lowZeroPanelP1J0I6Value_eq,
    lowZeroPanelP1J0I7Value_eq,
    lowZeroPanelP1J1I0Value_eq,
    lowZeroPanelP1J1I1Value_eq,
    lowZeroPanelP1J1I2Value_eq,
    lowZeroPanelP1J1I3Value_eq,
    lowZeroPanelP1J1I4Value_eq,
    lowZeroPanelP1J1I5Value_eq,
    lowZeroPanelP1J1I6Value_eq,
    lowZeroPanelP1J1I7Value_eq,
    lowZeroPanelP1J2I0Value_eq,
    lowZeroPanelP1J2I1Value_eq,
    lowZeroPanelP1J2I2Value_eq,
    lowZeroPanelP1J2I3Value_eq,
    lowZeroPanelP1J2I4Value_eq,
    lowZeroPanelP1J2I5Value_eq,
    lowZeroPanelP1J2I6Value_eq,
    lowZeroPanelP1J2I7Value_eq,
    lowZeroPanelP1J3I0Value_eq,
    lowZeroPanelP1J3I1Value_eq,
    lowZeroPanelP1J3I2Value_eq,
    lowZeroPanelP1J3I3Value_eq,
    lowZeroPanelP1J3I4Value_eq,
    lowZeroPanelP1J3I5Value_eq,
    lowZeroPanelP1J3I6Value_eq,
    lowZeroPanelP1J3I7Value_eq,
    lowZeroPanelP1J4I0Value_eq,
    lowZeroPanelP1J4I1Value_eq,
    lowZeroPanelP1J4I2Value_eq,
    lowZeroPanelP1J4I3Value_eq,
    lowZeroPanelP1J4I4Value_eq,
    lowZeroPanelP1J4I5Value_eq,
    lowZeroPanelP1J4I6Value_eq,
    lowZeroPanelP1J4I7Value_eq]

theorem lowZeroEndpointP1_error :
    |(F (lowZeroEndpointP1Point:ℂ)).re-
      (1-((1+(lowZeroEndpointP1Point:ℝ)^2)/4)*(lowZeroEndpointP1Quadrature:ℝ))/8|≤4/(10:ℝ)^39 := by
  rw [lowZeroEndpointP1_quadrature_cast]
  exact F_lowZero_storedQuadrature_error lowZeroEndpointP1Point
    (by norm_num [lowZeroEndpointP1Point,lowZeroSeedP1J0I0K1Point]) _
    (fun j hj i hi ↦ lowZeroEndpointP1_panel_error j i hj hi)

theorem lowZeroEndpointP1_sign : (F (lowZeroEndpointP1Point:ℂ)).re<0 := by
  have he := lowZeroEndpointP1_error
  rw [lowZeroEndpointP1_quadrature_eq] at he
  norm_num [lowZeroEndpointP1Point,lowZeroSeedP1J0I0K1Point] at he ⊢
  obtain ⟨hl,hu⟩ := abs_le.mp he
  linarith

end ReciprocalXi
