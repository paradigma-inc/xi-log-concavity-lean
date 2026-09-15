import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I1K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I1K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I1K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J1I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J1I1K1State n
  | 1 => lowZeroCoefficientsP0J1I1K2State n
  | 2 => lowZeroCoefficientsP0J1I1K3State n
  | 3 => lowZeroCoefficientsP0J1I1K4State n
  | 4 => lowZeroCoefficientsP0J1I1K5State n
  | _ => (0,0)

theorem lowZeroPanelP0J1I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J1I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J1I1K1Point)
        (theta48PanelCenter 1 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J1I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I1Coefficient,lowZeroSeedP0J1I1K1Point,lowZeroSeedP0J1I1K1Point]
  · convert lowZeroCoefficientsP0J1I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I1Coefficient,lowZeroSeedP0J1I1K1Point,lowZeroSeedP0J1I1K2Point]
  · convert lowZeroCoefficientsP0J1I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I1Coefficient,lowZeroSeedP0J1I1K1Point,lowZeroSeedP0J1I1K3Point]
  · convert lowZeroCoefficientsP0J1I1K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I1Coefficient,lowZeroSeedP0J1I1K1Point,lowZeroSeedP0J1I1K4Point]
  · convert lowZeroCoefficientsP0J1I1K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I1Coefficient,lowZeroSeedP0J1I1K1Point,lowZeroSeedP0J1I1K5Point]

def lowZeroPanelP0J1I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP0J1I1Coefficient

theorem lowZeroPanelP0J1I1Value_eq : lowZeroPanelP0J1I1Value=(146086313364339062030020019775929856128089336873038095342332181473232163979567827023908230686028994198502228180459232491471629842274823820822849946832559071384586903264507970234441970269:ℚ)/989030153895698639723079268687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J1I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J1I1K1Point (theta48PanelCenter 1 1)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP0J1I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J1I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J1I1K1Point (theta48PanelCenter 1 1)
    ((1:ℚ)/8) lowZeroPanelP0J1I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J1I1Value,theta48PanelHalfWidth]

end ReciprocalXi
