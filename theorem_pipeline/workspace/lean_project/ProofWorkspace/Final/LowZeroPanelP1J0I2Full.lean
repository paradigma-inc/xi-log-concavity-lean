import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I2K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I2K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I2K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I2K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J0I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J0I2K1State n
  | 1 => lowZeroCoefficientsP1J0I2K2State n
  | 2 => lowZeroCoefficientsP1J0I2K3State n
  | 3 => lowZeroCoefficientsP1J0I2K4State n
  | 4 => lowZeroCoefficientsP1J0I2K5State n
  | _ => (0,0)

theorem lowZeroPanelP1J0I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J0I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J0I2K1Point)
        (theta48PanelCenter 0 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J0I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I2Coefficient,lowZeroSeedP1J0I2K1Point,lowZeroSeedP1J0I2K1Point]
  · convert lowZeroCoefficientsP1J0I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I2Coefficient,lowZeroSeedP1J0I2K1Point,lowZeroSeedP1J0I2K2Point]
  · convert lowZeroCoefficientsP1J0I2K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I2Coefficient,lowZeroSeedP1J0I2K1Point,lowZeroSeedP1J0I2K3Point]
  · convert lowZeroCoefficientsP1J0I2K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I2Coefficient,lowZeroSeedP1J0I2K1Point,lowZeroSeedP1J0I2K4Point]
  · convert lowZeroCoefficientsP1J0I2K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I2Coefficient,lowZeroSeedP1J0I2K1Point,lowZeroSeedP1J0I2K5Point]

def lowZeroPanelP1J0I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP1J0I2Coefficient

theorem lowZeroPanelP1J0I2Value_eq : lowZeroPanelP1J0I2Value=(-20989040805764485553438202452036648413893323334158638754305383591905254318363655254939858458127958918819400386375155351468278886292286942822394533729535721333390125840068437855985770307963001:ℚ)/20271162034246239319764232691019000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J0I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J0I2K1Point (theta48PanelCenter 0 2)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP1J0I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J0I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J0I2K1Point (theta48PanelCenter 0 2)
    ((1:ℚ)/16) lowZeroPanelP1J0I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J0I2Value,theta48PanelHalfWidth]

end ReciprocalXi
