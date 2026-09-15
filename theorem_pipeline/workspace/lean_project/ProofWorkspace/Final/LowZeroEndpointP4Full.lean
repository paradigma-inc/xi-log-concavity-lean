import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroPanelP4J0I0Full
import ProofWorkspace.Final.LowZeroPanelP4J0I1Full
import ProofWorkspace.Final.LowZeroPanelP4J0I2Full
import ProofWorkspace.Final.LowZeroPanelP4J0I3Full
import ProofWorkspace.Final.LowZeroPanelP4J0I4Full
import ProofWorkspace.Final.LowZeroPanelP4J0I5Full
import ProofWorkspace.Final.LowZeroPanelP4J0I6Full
import ProofWorkspace.Final.LowZeroPanelP4J0I7Full
import ProofWorkspace.Final.LowZeroPanelP4J1I0Full
import ProofWorkspace.Final.LowZeroPanelP4J1I1Full
import ProofWorkspace.Final.LowZeroPanelP4J1I2Full
import ProofWorkspace.Final.LowZeroPanelP4J1I3Full
import ProofWorkspace.Final.LowZeroPanelP4J1I4Full
import ProofWorkspace.Final.LowZeroPanelP4J1I5Full
import ProofWorkspace.Final.LowZeroPanelP4J1I6Full
import ProofWorkspace.Final.LowZeroPanelP4J1I7Full
import ProofWorkspace.Final.LowZeroPanelP4J2I0Full
import ProofWorkspace.Final.LowZeroPanelP4J2I1Full
import ProofWorkspace.Final.LowZeroPanelP4J2I2Full
import ProofWorkspace.Final.LowZeroPanelP4J2I3Full
import ProofWorkspace.Final.LowZeroPanelP4J2I4Full
import ProofWorkspace.Final.LowZeroPanelP4J2I5Full
import ProofWorkspace.Final.LowZeroPanelP4J2I6Full
import ProofWorkspace.Final.LowZeroPanelP4J2I7Full
import ProofWorkspace.Final.LowZeroPanelP4J3I0Full
import ProofWorkspace.Final.LowZeroPanelP4J3I1Full
import ProofWorkspace.Final.LowZeroPanelP4J3I2Full
import ProofWorkspace.Final.LowZeroPanelP4J3I3Full
import ProofWorkspace.Final.LowZeroPanelP4J3I4Full
import ProofWorkspace.Final.LowZeroPanelP4J3I5Full
import ProofWorkspace.Final.LowZeroPanelP4J3I6Full
import ProofWorkspace.Final.LowZeroPanelP4J3I7Full
import ProofWorkspace.Final.LowZeroPanelP4J4I0Full
import ProofWorkspace.Final.LowZeroPanelP4J4I1Full
import ProofWorkspace.Final.LowZeroPanelP4J4I2Full
import ProofWorkspace.Final.LowZeroPanelP4J4I3Full
import ProofWorkspace.Final.LowZeroPanelP4J4I4Full
import ProofWorkspace.Final.LowZeroPanelP4J4I5Full
import ProofWorkspace.Final.LowZeroPanelP4J4I6Full
import ProofWorkspace.Final.LowZeroPanelP4J4I7Full

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace ReciprocalXi

def lowZeroEndpointP4Point : ℚ := lowZeroSeedP4J0I0K1Point

def lowZeroEndpointP4Panel (j i : ℕ) : ℚ :=
  match j, i with
  | 0, 0 => lowZeroPanelP4J0I0Value
  | 0, 1 => lowZeroPanelP4J0I1Value
  | 0, 2 => lowZeroPanelP4J0I2Value
  | 0, 3 => lowZeroPanelP4J0I3Value
  | 0, 4 => lowZeroPanelP4J0I4Value
  | 0, 5 => lowZeroPanelP4J0I5Value
  | 0, 6 => lowZeroPanelP4J0I6Value
  | 0, 7 => lowZeroPanelP4J0I7Value
  | 1, 0 => lowZeroPanelP4J1I0Value
  | 1, 1 => lowZeroPanelP4J1I1Value
  | 1, 2 => lowZeroPanelP4J1I2Value
  | 1, 3 => lowZeroPanelP4J1I3Value
  | 1, 4 => lowZeroPanelP4J1I4Value
  | 1, 5 => lowZeroPanelP4J1I5Value
  | 1, 6 => lowZeroPanelP4J1I6Value
  | 1, 7 => lowZeroPanelP4J1I7Value
  | 2, 0 => lowZeroPanelP4J2I0Value
  | 2, 1 => lowZeroPanelP4J2I1Value
  | 2, 2 => lowZeroPanelP4J2I2Value
  | 2, 3 => lowZeroPanelP4J2I3Value
  | 2, 4 => lowZeroPanelP4J2I4Value
  | 2, 5 => lowZeroPanelP4J2I5Value
  | 2, 6 => lowZeroPanelP4J2I6Value
  | 2, 7 => lowZeroPanelP4J2I7Value
  | 3, 0 => lowZeroPanelP4J3I0Value
  | 3, 1 => lowZeroPanelP4J3I1Value
  | 3, 2 => lowZeroPanelP4J3I2Value
  | 3, 3 => lowZeroPanelP4J3I3Value
  | 3, 4 => lowZeroPanelP4J3I4Value
  | 3, 5 => lowZeroPanelP4J3I5Value
  | 3, 6 => lowZeroPanelP4J3I6Value
  | 3, 7 => lowZeroPanelP4J3I7Value
  | 4, 0 => lowZeroPanelP4J4I0Value
  | 4, 1 => lowZeroPanelP4J4I1Value
  | 4, 2 => lowZeroPanelP4J4I2Value
  | 4, 3 => lowZeroPanelP4J4I3Value
  | 4, 4 => lowZeroPanelP4J4I4Value
  | 4, 5 => lowZeroPanelP4J4I5Value
  | 4, 6 => lowZeroPanelP4J4I6Value
  | 4, 7 => lowZeroPanelP4J4I7Value
  | _, _ => 0

theorem lowZeroEndpointP4_panel_error (j i : ℕ) (hj : j<5) (hi : i<8) :
    |lowZeroThetaTaylorPanelValue lowZeroEndpointP4Point (theta48PanelCenter j i)
      (theta48PanelHalfWidth j) 80-(lowZeroEndpointP4Panel j i:ℝ)|≤1600/(10:ℝ)^50 := by
  interval_cases j <;> interval_cases i
  · exact lowZeroPanelP4J0I0_panel_error
  · exact lowZeroPanelP4J0I1_panel_error
  · exact lowZeroPanelP4J0I2_panel_error
  · exact lowZeroPanelP4J0I3_panel_error
  · exact lowZeroPanelP4J0I4_panel_error
  · exact lowZeroPanelP4J0I5_panel_error
  · exact lowZeroPanelP4J0I6_panel_error
  · exact lowZeroPanelP4J0I7_panel_error
  · exact lowZeroPanelP4J1I0_panel_error
  · exact lowZeroPanelP4J1I1_panel_error
  · exact lowZeroPanelP4J1I2_panel_error
  · exact lowZeroPanelP4J1I3_panel_error
  · exact lowZeroPanelP4J1I4_panel_error
  · exact lowZeroPanelP4J1I5_panel_error
  · exact lowZeroPanelP4J1I6_panel_error
  · exact lowZeroPanelP4J1I7_panel_error
  · exact lowZeroPanelP4J2I0_panel_error
  · exact lowZeroPanelP4J2I1_panel_error
  · exact lowZeroPanelP4J2I2_panel_error
  · exact lowZeroPanelP4J2I3_panel_error
  · exact lowZeroPanelP4J2I4_panel_error
  · exact lowZeroPanelP4J2I5_panel_error
  · exact lowZeroPanelP4J2I6_panel_error
  · exact lowZeroPanelP4J2I7_panel_error
  · exact lowZeroPanelP4J3I0_panel_error
  · exact lowZeroPanelP4J3I1_panel_error
  · exact lowZeroPanelP4J3I2_panel_error
  · exact lowZeroPanelP4J3I3_panel_error
  · exact lowZeroPanelP4J3I4_panel_error
  · exact lowZeroPanelP4J3I5_panel_error
  · exact lowZeroPanelP4J3I6_panel_error
  · exact lowZeroPanelP4J3I7_panel_error
  · exact lowZeroPanelP4J4I0_panel_error
  · exact lowZeroPanelP4J4I1_panel_error
  · exact lowZeroPanelP4J4I2_panel_error
  · exact lowZeroPanelP4J4I3_panel_error
  · exact lowZeroPanelP4J4I4_panel_error
  · exact lowZeroPanelP4J4I5_panel_error
  · exact lowZeroPanelP4J4I6_panel_error
  · exact lowZeroPanelP4J4I7_panel_error

def lowZeroEndpointP4Quadrature : ℚ :=
  ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 8, lowZeroEndpointP4Panel j i

theorem lowZeroEndpointP4_quadrature_cast : (lowZeroEndpointP4Quadrature:ℝ)=
    lowZeroStoredQuadrature (fun j i ↦ (lowZeroEndpointP4Panel j i:ℝ)) := by
  unfold lowZeroEndpointP4Quadrature lowZeroStoredQuadrature
  push_cast <;> rfl

theorem lowZeroEndpointP4_quadrature_eq : lowZeroEndpointP4Quadrature=(131677884075302663352025625787605643161054626432997230428487860546576386739390563073558743652722477485182181803810913223699451799373787940604275886577217765884574130485276171027347334822027:ℚ)/82403097700187964714488750776500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  norm_num [lowZeroEndpointP4Quadrature,lowZeroEndpointP4Panel,Finset.sum_range_succ,
    lowZeroPanelP4J0I0Value_eq,
    lowZeroPanelP4J0I1Value_eq,
    lowZeroPanelP4J0I2Value_eq,
    lowZeroPanelP4J0I3Value_eq,
    lowZeroPanelP4J0I4Value_eq,
    lowZeroPanelP4J0I5Value_eq,
    lowZeroPanelP4J0I6Value_eq,
    lowZeroPanelP4J0I7Value_eq,
    lowZeroPanelP4J1I0Value_eq,
    lowZeroPanelP4J1I1Value_eq,
    lowZeroPanelP4J1I2Value_eq,
    lowZeroPanelP4J1I3Value_eq,
    lowZeroPanelP4J1I4Value_eq,
    lowZeroPanelP4J1I5Value_eq,
    lowZeroPanelP4J1I6Value_eq,
    lowZeroPanelP4J1I7Value_eq,
    lowZeroPanelP4J2I0Value_eq,
    lowZeroPanelP4J2I1Value_eq,
    lowZeroPanelP4J2I2Value_eq,
    lowZeroPanelP4J2I3Value_eq,
    lowZeroPanelP4J2I4Value_eq,
    lowZeroPanelP4J2I5Value_eq,
    lowZeroPanelP4J2I6Value_eq,
    lowZeroPanelP4J2I7Value_eq,
    lowZeroPanelP4J3I0Value_eq,
    lowZeroPanelP4J3I1Value_eq,
    lowZeroPanelP4J3I2Value_eq,
    lowZeroPanelP4J3I3Value_eq,
    lowZeroPanelP4J3I4Value_eq,
    lowZeroPanelP4J3I5Value_eq,
    lowZeroPanelP4J3I6Value_eq,
    lowZeroPanelP4J3I7Value_eq,
    lowZeroPanelP4J4I0Value_eq,
    lowZeroPanelP4J4I1Value_eq,
    lowZeroPanelP4J4I2Value_eq,
    lowZeroPanelP4J4I3Value_eq,
    lowZeroPanelP4J4I4Value_eq,
    lowZeroPanelP4J4I5Value_eq,
    lowZeroPanelP4J4I6Value_eq,
    lowZeroPanelP4J4I7Value_eq]

theorem lowZeroEndpointP4_error :
    |(F (lowZeroEndpointP4Point:ℂ)).re-
      (1-((1+(lowZeroEndpointP4Point:ℝ)^2)/4)*(lowZeroEndpointP4Quadrature:ℝ))/8|≤4/(10:ℝ)^39 := by
  rw [lowZeroEndpointP4_quadrature_cast]
  exact F_lowZero_storedQuadrature_error lowZeroEndpointP4Point
    (by norm_num [lowZeroEndpointP4Point,lowZeroSeedP4J0I0K1Point]) _
    (fun j hj i hi ↦ lowZeroEndpointP4_panel_error j i hj hi)

theorem lowZeroEndpointP4_sign : 0<(F (lowZeroEndpointP4Point:ℂ)).re := by
  have he := lowZeroEndpointP4_error
  rw [lowZeroEndpointP4_quadrature_eq] at he
  norm_num [lowZeroEndpointP4Point,lowZeroSeedP4J0I0K1Point] at he ⊢
  obtain ⟨hl,hu⟩ := abs_le.mp he
  linarith

end ReciprocalXi
