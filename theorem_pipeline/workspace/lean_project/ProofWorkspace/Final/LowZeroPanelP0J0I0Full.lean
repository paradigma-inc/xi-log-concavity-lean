import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I0K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I0K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I0K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I0K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J0I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J0I0K1State n
  | 1 => lowZeroCoefficientsP0J0I0K2State n
  | 2 => lowZeroCoefficientsP0J0I0K3State n
  | 3 => lowZeroCoefficientsP0J0I0K4State n
  | 4 => lowZeroCoefficientsP0J0I0K5State n
  | _ => (0,0)

theorem lowZeroPanelP0J0I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J0I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J0I0K1Point)
        (theta48PanelCenter 0 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J0I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I0Coefficient,lowZeroSeedP0J0I0K1Point,lowZeroSeedP0J0I0K1Point]
  · convert lowZeroCoefficientsP0J0I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I0Coefficient,lowZeroSeedP0J0I0K1Point,lowZeroSeedP0J0I0K2Point]
  · convert lowZeroCoefficientsP0J0I0K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I0Coefficient,lowZeroSeedP0J0I0K1Point,lowZeroSeedP0J0I0K3Point]
  · convert lowZeroCoefficientsP0J0I0K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I0Coefficient,lowZeroSeedP0J0I0K1Point,lowZeroSeedP0J0I0K4Point]
  · convert lowZeroCoefficientsP0J0I0K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I0Coefficient,lowZeroSeedP0J0I0K1Point,lowZeroSeedP0J0I0K5Point]

def lowZeroPanelP0J0I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP0J0I0Coefficient

theorem lowZeroPanelP0J0I0Value_eq : lowZeroPanelP0J0I0Value=(25043742717428534130045605015161552695643590619951481428848863986241992352745872053181197265189366778732094987239245290069142975783757033659600147645262420672460999965165711820570547307643:ℚ)/3253275884167266782180104749000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J0I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J0I0K1Point (theta48PanelCenter 0 0)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP0J0I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J0I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J0I0K1Point (theta48PanelCenter 0 0)
    ((1:ℚ)/16) lowZeroPanelP0J0I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J0I0Value,theta48PanelHalfWidth]

end ReciprocalXi
