import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I3K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I3K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I3K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I3K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J0I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J0I3K1State n
  | 1 => lowZeroCoefficientsP3J0I3K2State n
  | 2 => lowZeroCoefficientsP3J0I3K3State n
  | 3 => lowZeroCoefficientsP3J0I3K4State n
  | 4 => lowZeroCoefficientsP3J0I3K5State n
  | _ => (0,0)

theorem lowZeroPanelP3J0I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J0I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J0I3K1Point)
        (theta48PanelCenter 0 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J0I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I3Coefficient,lowZeroSeedP3J0I3K1Point,lowZeroSeedP3J0I3K1Point]
  · convert lowZeroCoefficientsP3J0I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I3Coefficient,lowZeroSeedP3J0I3K1Point,lowZeroSeedP3J0I3K2Point]
  · convert lowZeroCoefficientsP3J0I3K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I3Coefficient,lowZeroSeedP3J0I3K1Point,lowZeroSeedP3J0I3K3Point]
  · convert lowZeroCoefficientsP3J0I3K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I3Coefficient,lowZeroSeedP3J0I3K1Point,lowZeroSeedP3J0I3K4Point]
  · convert lowZeroCoefficientsP3J0I3K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I3Coefficient,lowZeroSeedP3J0I3K1Point,lowZeroSeedP3J0I3K5Point]

def lowZeroPanelP3J0I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP3J0I3Coefficient

theorem lowZeroPanelP3J0I3Value_eq : lowZeroPanelP3J0I3Value=(-1273935916097909304836656307204522966837247152775161277003494090511461073074336763399524903766633960059523142102596698430285419694369236762424519352649020828797553487790932686590486155503373:ℚ)/779660078240239973837085872731500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J0I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J0I3K1Point (theta48PanelCenter 0 3)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP3J0I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J0I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J0I3K1Point (theta48PanelCenter 0 3)
    ((1:ℚ)/16) lowZeroPanelP3J0I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J0I3Value,theta48PanelHalfWidth]

end ReciprocalXi
