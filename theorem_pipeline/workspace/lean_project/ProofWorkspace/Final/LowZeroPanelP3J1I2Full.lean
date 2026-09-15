import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I2K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I2K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I2K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I2K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J1I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J1I2K1State n
  | 1 => lowZeroCoefficientsP3J1I2K2State n
  | 2 => lowZeroCoefficientsP3J1I2K3State n
  | 3 => lowZeroCoefficientsP3J1I2K4State n
  | 4 => lowZeroCoefficientsP3J1I2K5State n
  | _ => (0,0)

theorem lowZeroPanelP3J1I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J1I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J1I2K1Point)
        (theta48PanelCenter 1 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J1I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I2Coefficient,lowZeroSeedP3J1I2K1Point,lowZeroSeedP3J1I2K1Point]
  · convert lowZeroCoefficientsP3J1I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I2Coefficient,lowZeroSeedP3J1I2K1Point,lowZeroSeedP3J1I2K2Point]
  · convert lowZeroCoefficientsP3J1I2K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I2Coefficient,lowZeroSeedP3J1I2K1Point,lowZeroSeedP3J1I2K3Point]
  · convert lowZeroCoefficientsP3J1I2K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I2Coefficient,lowZeroSeedP3J1I2K1Point,lowZeroSeedP3J1I2K4Point]
  · convert lowZeroCoefficientsP3J1I2K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I2Coefficient,lowZeroSeedP3J1I2K1Point,lowZeroSeedP3J1I2K5Point]

def lowZeroPanelP3J1I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP3J1I2Coefficient

theorem lowZeroPanelP3J1I2Value_eq : lowZeroPanelP3J1I2Value=(-6849263991401129381958669586164543921272534393584959165633545601449181903768985861828798372143138278070276732556435892246276250314664287886519560992609814530783968559067276492228302789:ℚ)/136082773017589984826762749500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J1I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J1I2K1Point (theta48PanelCenter 1 2)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP3J1I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J1I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J1I2K1Point (theta48PanelCenter 1 2)
    ((1:ℚ)/8) lowZeroPanelP3J1I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J1I2Value,theta48PanelHalfWidth]

end ReciprocalXi
