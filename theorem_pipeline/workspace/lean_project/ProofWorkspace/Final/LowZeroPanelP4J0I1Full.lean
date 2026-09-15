import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I1K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I1K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I1K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J0I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J0I1K1State n
  | 1 => lowZeroCoefficientsP4J0I1K2State n
  | 2 => lowZeroCoefficientsP4J0I1K3State n
  | 3 => lowZeroCoefficientsP4J0I1K4State n
  | 4 => lowZeroCoefficientsP4J0I1K5State n
  | _ => (0,0)

theorem lowZeroPanelP4J0I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J0I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J0I1K1Point)
        (theta48PanelCenter 0 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J0I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I1Coefficient,lowZeroSeedP4J0I1K1Point,lowZeroSeedP4J0I1K1Point]
  · convert lowZeroCoefficientsP4J0I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I1Coefficient,lowZeroSeedP4J0I1K1Point,lowZeroSeedP4J0I1K2Point]
  · convert lowZeroCoefficientsP4J0I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I1Coefficient,lowZeroSeedP4J0I1K1Point,lowZeroSeedP4J0I1K3Point]
  · convert lowZeroCoefficientsP4J0I1K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I1Coefficient,lowZeroSeedP4J0I1K1Point,lowZeroSeedP4J0I1K4Point]
  · convert lowZeroCoefficientsP4J0I1K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I1Coefficient,lowZeroSeedP4J0I1K1Point,lowZeroSeedP4J0I1K5Point]

def lowZeroPanelP4J0I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP4J0I1Coefficient

theorem lowZeroPanelP4J0I1Value_eq : lowZeroPanelP4J0I1Value=(-701356149380713881707820429780671034487153973260630686833264301450264835024002533315144748845649944934922523913872216467060776333013704015407966141938340920034875992762641993083133968622443:ℚ)/285509324426003370700904685789000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J0I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J0I1K1Point (theta48PanelCenter 0 1)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP4J0I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J0I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J0I1K1Point (theta48PanelCenter 0 1)
    ((1:ℚ)/16) lowZeroPanelP4J0I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J0I1Value,theta48PanelHalfWidth]

end ReciprocalXi
