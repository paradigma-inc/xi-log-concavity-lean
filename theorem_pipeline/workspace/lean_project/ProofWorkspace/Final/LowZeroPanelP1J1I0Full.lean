import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I0K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I0K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I0K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I0K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J1I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J1I0K1State n
  | 1 => lowZeroCoefficientsP1J1I0K2State n
  | 2 => lowZeroCoefficientsP1J1I0K3State n
  | 3 => lowZeroCoefficientsP1J1I0K4State n
  | 4 => lowZeroCoefficientsP1J1I0K5State n
  | _ => (0,0)

theorem lowZeroPanelP1J1I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J1I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J1I0K1Point)
        (theta48PanelCenter 1 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J1I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I0Coefficient,lowZeroSeedP1J1I0K1Point,lowZeroSeedP1J1I0K1Point]
  · convert lowZeroCoefficientsP1J1I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I0Coefficient,lowZeroSeedP1J1I0K1Point,lowZeroSeedP1J1I0K2Point]
  · convert lowZeroCoefficientsP1J1I0K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I0Coefficient,lowZeroSeedP1J1I0K1Point,lowZeroSeedP1J1I0K3Point]
  · convert lowZeroCoefficientsP1J1I0K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I0Coefficient,lowZeroSeedP1J1I0K1Point,lowZeroSeedP1J1I0K4Point]
  · convert lowZeroCoefficientsP1J1I0K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I0Coefficient,lowZeroSeedP1J1I0K1Point,lowZeroSeedP1J1I0K5Point]

def lowZeroPanelP1J1I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP1J1I0Coefficient

theorem lowZeroPanelP1J1I0Value_eq : lowZeroPanelP1J1I0Value=(45375739769795808136996493310427388781352246640966830185950455149652751258289022836107687168972939037860066509209514045147636163414072395045019537541355492639149523855830135710607853513327:ℚ)/241323357550550468092431341559750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J1I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J1I0K1Point (theta48PanelCenter 1 0)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP1J1I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J1I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J1I0K1Point (theta48PanelCenter 1 0)
    ((1:ℚ)/8) lowZeroPanelP1J1I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J1I0Value,theta48PanelHalfWidth]

end ReciprocalXi
