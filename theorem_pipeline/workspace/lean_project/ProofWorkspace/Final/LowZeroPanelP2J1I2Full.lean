import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I2K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I2K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I2K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I2K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J1I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J1I2K1State n
  | 1 => lowZeroCoefficientsP2J1I2K2State n
  | 2 => lowZeroCoefficientsP2J1I2K3State n
  | 3 => lowZeroCoefficientsP2J1I2K4State n
  | 4 => lowZeroCoefficientsP2J1I2K5State n
  | _ => (0,0)

theorem lowZeroPanelP2J1I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J1I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J1I2K1Point)
        (theta48PanelCenter 1 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J1I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I2Coefficient,lowZeroSeedP2J1I2K1Point,lowZeroSeedP2J1I2K1Point]
  · convert lowZeroCoefficientsP2J1I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I2Coefficient,lowZeroSeedP2J1I2K1Point,lowZeroSeedP2J1I2K2Point]
  · convert lowZeroCoefficientsP2J1I2K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I2Coefficient,lowZeroSeedP2J1I2K1Point,lowZeroSeedP2J1I2K3Point]
  · convert lowZeroCoefficientsP2J1I2K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I2Coefficient,lowZeroSeedP2J1I2K1Point,lowZeroSeedP2J1I2K4Point]
  · convert lowZeroCoefficientsP2J1I2K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I2Coefficient,lowZeroSeedP2J1I2K1Point,lowZeroSeedP2J1I2K5Point]

def lowZeroPanelP2J1I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP2J1I2Coefficient

theorem lowZeroPanelP2J1I2Value_eq : lowZeroPanelP2J1I2Value=(-46376366485777047045242151768256812075443005458074379840569304311322010527685977856495954218458633373713268667014467002697414892278978763194244203758746584236072751087619359608862509030613:ℚ)/921416456102101787262010576864500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J1I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J1I2K1Point (theta48PanelCenter 1 2)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP2J1I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J1I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J1I2K1Point (theta48PanelCenter 1 2)
    ((1:ℚ)/8) lowZeroPanelP2J1I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J1I2Value,theta48PanelHalfWidth]

end ReciprocalXi
