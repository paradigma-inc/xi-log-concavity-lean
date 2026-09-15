import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroPanelP3J0I0Full
import ProofWorkspace.Final.LowZeroPanelP3J0I1Full
import ProofWorkspace.Final.LowZeroPanelP3J0I2Full
import ProofWorkspace.Final.LowZeroPanelP3J0I3Full
import ProofWorkspace.Final.LowZeroPanelP3J0I4Full
import ProofWorkspace.Final.LowZeroPanelP3J0I5Full
import ProofWorkspace.Final.LowZeroPanelP3J0I6Full
import ProofWorkspace.Final.LowZeroPanelP3J0I7Full
import ProofWorkspace.Final.LowZeroPanelP3J1I0Full
import ProofWorkspace.Final.LowZeroPanelP3J1I1Full
import ProofWorkspace.Final.LowZeroPanelP3J1I2Full
import ProofWorkspace.Final.LowZeroPanelP3J1I3Full
import ProofWorkspace.Final.LowZeroPanelP3J1I4Full
import ProofWorkspace.Final.LowZeroPanelP3J1I5Full
import ProofWorkspace.Final.LowZeroPanelP3J1I6Full
import ProofWorkspace.Final.LowZeroPanelP3J1I7Full
import ProofWorkspace.Final.LowZeroPanelP3J2I0Full
import ProofWorkspace.Final.LowZeroPanelP3J2I1Full
import ProofWorkspace.Final.LowZeroPanelP3J2I2Full
import ProofWorkspace.Final.LowZeroPanelP3J2I3Full
import ProofWorkspace.Final.LowZeroPanelP3J2I4Full
import ProofWorkspace.Final.LowZeroPanelP3J2I5Full
import ProofWorkspace.Final.LowZeroPanelP3J2I6Full
import ProofWorkspace.Final.LowZeroPanelP3J2I7Full
import ProofWorkspace.Final.LowZeroPanelP3J3I0Full
import ProofWorkspace.Final.LowZeroPanelP3J3I1Full
import ProofWorkspace.Final.LowZeroPanelP3J3I2Full
import ProofWorkspace.Final.LowZeroPanelP3J3I3Full
import ProofWorkspace.Final.LowZeroPanelP3J3I4Full
import ProofWorkspace.Final.LowZeroPanelP3J3I5Full
import ProofWorkspace.Final.LowZeroPanelP3J3I6Full
import ProofWorkspace.Final.LowZeroPanelP3J3I7Full
import ProofWorkspace.Final.LowZeroPanelP3J4I0Full
import ProofWorkspace.Final.LowZeroPanelP3J4I1Full
import ProofWorkspace.Final.LowZeroPanelP3J4I2Full
import ProofWorkspace.Final.LowZeroPanelP3J4I3Full
import ProofWorkspace.Final.LowZeroPanelP3J4I4Full
import ProofWorkspace.Final.LowZeroPanelP3J4I5Full
import ProofWorkspace.Final.LowZeroPanelP3J4I6Full
import ProofWorkspace.Final.LowZeroPanelP3J4I7Full

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace ReciprocalXi

def lowZeroEndpointP3Point : ℚ := lowZeroSeedP3J0I0K1Point

def lowZeroEndpointP3Panel (j i : ℕ) : ℚ :=
  match j, i with
  | 0, 0 => lowZeroPanelP3J0I0Value
  | 0, 1 => lowZeroPanelP3J0I1Value
  | 0, 2 => lowZeroPanelP3J0I2Value
  | 0, 3 => lowZeroPanelP3J0I3Value
  | 0, 4 => lowZeroPanelP3J0I4Value
  | 0, 5 => lowZeroPanelP3J0I5Value
  | 0, 6 => lowZeroPanelP3J0I6Value
  | 0, 7 => lowZeroPanelP3J0I7Value
  | 1, 0 => lowZeroPanelP3J1I0Value
  | 1, 1 => lowZeroPanelP3J1I1Value
  | 1, 2 => lowZeroPanelP3J1I2Value
  | 1, 3 => lowZeroPanelP3J1I3Value
  | 1, 4 => lowZeroPanelP3J1I4Value
  | 1, 5 => lowZeroPanelP3J1I5Value
  | 1, 6 => lowZeroPanelP3J1I6Value
  | 1, 7 => lowZeroPanelP3J1I7Value
  | 2, 0 => lowZeroPanelP3J2I0Value
  | 2, 1 => lowZeroPanelP3J2I1Value
  | 2, 2 => lowZeroPanelP3J2I2Value
  | 2, 3 => lowZeroPanelP3J2I3Value
  | 2, 4 => lowZeroPanelP3J2I4Value
  | 2, 5 => lowZeroPanelP3J2I5Value
  | 2, 6 => lowZeroPanelP3J2I6Value
  | 2, 7 => lowZeroPanelP3J2I7Value
  | 3, 0 => lowZeroPanelP3J3I0Value
  | 3, 1 => lowZeroPanelP3J3I1Value
  | 3, 2 => lowZeroPanelP3J3I2Value
  | 3, 3 => lowZeroPanelP3J3I3Value
  | 3, 4 => lowZeroPanelP3J3I4Value
  | 3, 5 => lowZeroPanelP3J3I5Value
  | 3, 6 => lowZeroPanelP3J3I6Value
  | 3, 7 => lowZeroPanelP3J3I7Value
  | 4, 0 => lowZeroPanelP3J4I0Value
  | 4, 1 => lowZeroPanelP3J4I1Value
  | 4, 2 => lowZeroPanelP3J4I2Value
  | 4, 3 => lowZeroPanelP3J4I3Value
  | 4, 4 => lowZeroPanelP3J4I4Value
  | 4, 5 => lowZeroPanelP3J4I5Value
  | 4, 6 => lowZeroPanelP3J4I6Value
  | 4, 7 => lowZeroPanelP3J4I7Value
  | _, _ => 0

theorem lowZeroEndpointP3_panel_error (j i : ℕ) (hj : j<5) (hi : i<8) :
    |lowZeroThetaTaylorPanelValue lowZeroEndpointP3Point (theta48PanelCenter j i)
      (theta48PanelHalfWidth j) 80-(lowZeroEndpointP3Panel j i:ℝ)|≤1600/(10:ℝ)^50 := by
  interval_cases j <;> interval_cases i
  · exact lowZeroPanelP3J0I0_panel_error
  · exact lowZeroPanelP3J0I1_panel_error
  · exact lowZeroPanelP3J0I2_panel_error
  · exact lowZeroPanelP3J0I3_panel_error
  · exact lowZeroPanelP3J0I4_panel_error
  · exact lowZeroPanelP3J0I5_panel_error
  · exact lowZeroPanelP3J0I6_panel_error
  · exact lowZeroPanelP3J0I7_panel_error
  · exact lowZeroPanelP3J1I0_panel_error
  · exact lowZeroPanelP3J1I1_panel_error
  · exact lowZeroPanelP3J1I2_panel_error
  · exact lowZeroPanelP3J1I3_panel_error
  · exact lowZeroPanelP3J1I4_panel_error
  · exact lowZeroPanelP3J1I5_panel_error
  · exact lowZeroPanelP3J1I6_panel_error
  · exact lowZeroPanelP3J1I7_panel_error
  · exact lowZeroPanelP3J2I0_panel_error
  · exact lowZeroPanelP3J2I1_panel_error
  · exact lowZeroPanelP3J2I2_panel_error
  · exact lowZeroPanelP3J2I3_panel_error
  · exact lowZeroPanelP3J2I4_panel_error
  · exact lowZeroPanelP3J2I5_panel_error
  · exact lowZeroPanelP3J2I6_panel_error
  · exact lowZeroPanelP3J2I7_panel_error
  · exact lowZeroPanelP3J3I0_panel_error
  · exact lowZeroPanelP3J3I1_panel_error
  · exact lowZeroPanelP3J3I2_panel_error
  · exact lowZeroPanelP3J3I3_panel_error
  · exact lowZeroPanelP3J3I4_panel_error
  · exact lowZeroPanelP3J3I5_panel_error
  · exact lowZeroPanelP3J3I6_panel_error
  · exact lowZeroPanelP3J3I7_panel_error
  · exact lowZeroPanelP3J4I0_panel_error
  · exact lowZeroPanelP3J4I1_panel_error
  · exact lowZeroPanelP3J4I2_panel_error
  · exact lowZeroPanelP3J4I3_panel_error
  · exact lowZeroPanelP3J4I4_panel_error
  · exact lowZeroPanelP3J4I5_panel_error
  · exact lowZeroPanelP3J4I6_panel_error
  · exact lowZeroPanelP3J4I7_panel_error

def lowZeroEndpointP3Quadrature : ℚ :=
  ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 8, lowZeroEndpointP3Panel j i

theorem lowZeroEndpointP3_quadrature_cast : (lowZeroEndpointP3Quadrature:ℝ)=
    lowZeroStoredQuadrature (fun j i ↦ (lowZeroEndpointP3Panel j i:ℝ)) := by
  unfold lowZeroEndpointP3Quadrature lowZeroStoredQuadrature
  push_cast <;> rfl

theorem lowZeroEndpointP3_quadrature_eq : lowZeroEndpointP3Quadrature=(804282232752079568255250311834158473074221691074570535213495933218765038561871361094017589534833391620647819794983074631357239829242795936146222446678370789450021191531920874328114281731673:ℚ)/355634421653442795083583029667000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  norm_num [lowZeroEndpointP3Quadrature,lowZeroEndpointP3Panel,Finset.sum_range_succ,
    lowZeroPanelP3J0I0Value_eq,
    lowZeroPanelP3J0I1Value_eq,
    lowZeroPanelP3J0I2Value_eq,
    lowZeroPanelP3J0I3Value_eq,
    lowZeroPanelP3J0I4Value_eq,
    lowZeroPanelP3J0I5Value_eq,
    lowZeroPanelP3J0I6Value_eq,
    lowZeroPanelP3J0I7Value_eq,
    lowZeroPanelP3J1I0Value_eq,
    lowZeroPanelP3J1I1Value_eq,
    lowZeroPanelP3J1I2Value_eq,
    lowZeroPanelP3J1I3Value_eq,
    lowZeroPanelP3J1I4Value_eq,
    lowZeroPanelP3J1I5Value_eq,
    lowZeroPanelP3J1I6Value_eq,
    lowZeroPanelP3J1I7Value_eq,
    lowZeroPanelP3J2I0Value_eq,
    lowZeroPanelP3J2I1Value_eq,
    lowZeroPanelP3J2I2Value_eq,
    lowZeroPanelP3J2I3Value_eq,
    lowZeroPanelP3J2I4Value_eq,
    lowZeroPanelP3J2I5Value_eq,
    lowZeroPanelP3J2I6Value_eq,
    lowZeroPanelP3J2I7Value_eq,
    lowZeroPanelP3J3I0Value_eq,
    lowZeroPanelP3J3I1Value_eq,
    lowZeroPanelP3J3I2Value_eq,
    lowZeroPanelP3J3I3Value_eq,
    lowZeroPanelP3J3I4Value_eq,
    lowZeroPanelP3J3I5Value_eq,
    lowZeroPanelP3J3I6Value_eq,
    lowZeroPanelP3J3I7Value_eq,
    lowZeroPanelP3J4I0Value_eq,
    lowZeroPanelP3J4I1Value_eq,
    lowZeroPanelP3J4I2Value_eq,
    lowZeroPanelP3J4I3Value_eq,
    lowZeroPanelP3J4I4Value_eq,
    lowZeroPanelP3J4I5Value_eq,
    lowZeroPanelP3J4I6Value_eq,
    lowZeroPanelP3J4I7Value_eq]

theorem lowZeroEndpointP3_error :
    |(F (lowZeroEndpointP3Point:ℂ)).re-
      (1-((1+(lowZeroEndpointP3Point:ℝ)^2)/4)*(lowZeroEndpointP3Quadrature:ℝ))/8|≤4/(10:ℝ)^39 := by
  rw [lowZeroEndpointP3_quadrature_cast]
  exact F_lowZero_storedQuadrature_error lowZeroEndpointP3Point
    (by norm_num [lowZeroEndpointP3Point,lowZeroSeedP3J0I0K1Point]) _
    (fun j hj i hi ↦ lowZeroEndpointP3_panel_error j i hj hi)

theorem lowZeroEndpointP3_sign : 0<(F (lowZeroEndpointP3Point:ℂ)).re := by
  have he := lowZeroEndpointP3_error
  rw [lowZeroEndpointP3_quadrature_eq] at he
  norm_num [lowZeroEndpointP3Point,lowZeroSeedP3J0I0K1Point] at he ⊢
  obtain ⟨hl,hu⟩ := abs_le.mp he
  linarith

end ReciprocalXi
