import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I0K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I0K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I0K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I0K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J1I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J1I0K1State n
  | 1 => lowZeroCoefficientsP4J1I0K2State n
  | 2 => lowZeroCoefficientsP4J1I0K3State n
  | 3 => lowZeroCoefficientsP4J1I0K4State n
  | 4 => lowZeroCoefficientsP4J1I0K5State n
  | _ => (0,0)

theorem lowZeroPanelP4J1I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J1I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J1I0K1Point)
        (theta48PanelCenter 1 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J1I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I0Coefficient,lowZeroSeedP4J1I0K1Point,lowZeroSeedP4J1I0K1Point]
  · convert lowZeroCoefficientsP4J1I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I0Coefficient,lowZeroSeedP4J1I0K1Point,lowZeroSeedP4J1I0K2Point]
  · convert lowZeroCoefficientsP4J1I0K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I0Coefficient,lowZeroSeedP4J1I0K1Point,lowZeroSeedP4J1I0K3Point]
  · convert lowZeroCoefficientsP4J1I0K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I0Coefficient,lowZeroSeedP4J1I0K1Point,lowZeroSeedP4J1I0K4Point]
  · convert lowZeroCoefficientsP4J1I0K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I0Coefficient,lowZeroSeedP4J1I0K1Point,lowZeroSeedP4J1I0K5Point]

def lowZeroPanelP4J1I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP4J1I0Coefficient

theorem lowZeroPanelP4J1I0Value_eq : lowZeroPanelP4J1I0Value=(-262063504928362929461060147546856204694738556480313520654854326954622532154587350518854340003534984235915384789476806524040763638731395568391987760352227320751379993973886443366099276718429:ℚ)/779660078240239973837085872731500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J1I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J1I0K1Point (theta48PanelCenter 1 0)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP4J1I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J1I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J1I0K1Point (theta48PanelCenter 1 0)
    ((1:ℚ)/8) lowZeroPanelP4J1I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J1I0Value,theta48PanelHalfWidth]

end ReciprocalXi
