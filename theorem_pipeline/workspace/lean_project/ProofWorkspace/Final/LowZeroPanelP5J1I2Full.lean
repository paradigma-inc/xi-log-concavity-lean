import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I2K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I2K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I2K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I2K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J1I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J1I2K1State n
  | 1 => lowZeroCoefficientsP5J1I2K2State n
  | 2 => lowZeroCoefficientsP5J1I2K3State n
  | 3 => lowZeroCoefficientsP5J1I2K4State n
  | 4 => lowZeroCoefficientsP5J1I2K5State n
  | _ => (0,0)

theorem lowZeroPanelP5J1I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J1I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J1I2K1Point)
        (theta48PanelCenter 1 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J1I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I2Coefficient,lowZeroSeedP5J1I2K1Point,lowZeroSeedP5J1I2K1Point]
  · convert lowZeroCoefficientsP5J1I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I2Coefficient,lowZeroSeedP5J1I2K1Point,lowZeroSeedP5J1I2K2Point]
  · convert lowZeroCoefficientsP5J1I2K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I2Coefficient,lowZeroSeedP5J1I2K1Point,lowZeroSeedP5J1I2K3Point]
  · convert lowZeroCoefficientsP5J1I2K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I2Coefficient,lowZeroSeedP5J1I2K1Point,lowZeroSeedP5J1I2K4Point]
  · convert lowZeroCoefficientsP5J1I2K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I2Coefficient,lowZeroSeedP5J1I2K1Point,lowZeroSeedP5J1I2K5Point]

def lowZeroPanelP5J1I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP5J1I2Coefficient

theorem lowZeroPanelP5J1I2Value_eq : lowZeroPanelP5J1I2Value=(6684951165795596954214874004654751858493652481808790522599384251485927715029636217765870683746045551642139872228318610600459261160735231304633974509170215624212560810067661586806449888037:ℚ)/129943346373373328972847645455250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J1I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J1I2K1Point (theta48PanelCenter 1 2)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP5J1I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J1I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J1I2K1Point (theta48PanelCenter 1 2)
    ((1:ℚ)/8) lowZeroPanelP5J1I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J1I2Value,theta48PanelHalfWidth]

end ReciprocalXi
