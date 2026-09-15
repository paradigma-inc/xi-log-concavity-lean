import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I2K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I2K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I2K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I2K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J0I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J0I2K1State n
  | 1 => lowZeroCoefficientsP2J0I2K2State n
  | 2 => lowZeroCoefficientsP2J0I2K3State n
  | 3 => lowZeroCoefficientsP2J0I2K4State n
  | 4 => lowZeroCoefficientsP2J0I2K5State n
  | _ => (0,0)

theorem lowZeroPanelP2J0I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J0I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J0I2K1Point)
        (theta48PanelCenter 0 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J0I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I2Coefficient,lowZeroSeedP2J0I2K1Point,lowZeroSeedP2J0I2K1Point]
  · convert lowZeroCoefficientsP2J0I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I2Coefficient,lowZeroSeedP2J0I2K1Point,lowZeroSeedP2J0I2K2Point]
  · convert lowZeroCoefficientsP2J0I2K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I2Coefficient,lowZeroSeedP2J0I2K1Point,lowZeroSeedP2J0I2K3Point]
  · convert lowZeroCoefficientsP2J0I2K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I2Coefficient,lowZeroSeedP2J0I2K1Point,lowZeroSeedP2J0I2K4Point]
  · convert lowZeroCoefficientsP2J0I2K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I2Coefficient,lowZeroSeedP2J0I2K1Point,lowZeroSeedP2J0I2K5Point]

def lowZeroPanelP2J0I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP2J0I2Coefficient

theorem lowZeroPanelP2J0I2Value_eq : lowZeroPanelP2J0I2Value=(-12269372733136935865125035696938325368221291000831603587965628928650272270994417551935633907867376089722874723063482799711893235933308386099635522127698243855969952187728463228626449521626813:ℚ)/4054232406849247863952846538203800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J0I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J0I2K1Point (theta48PanelCenter 0 2)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP2J0I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J0I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J0I2K1Point (theta48PanelCenter 0 2)
    ((1:ℚ)/16) lowZeroPanelP2J0I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J0I2Value,theta48PanelHalfWidth]

end ReciprocalXi
