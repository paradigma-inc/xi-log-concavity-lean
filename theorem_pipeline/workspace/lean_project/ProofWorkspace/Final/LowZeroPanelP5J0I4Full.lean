import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I4K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I4K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I4K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J0I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J0I4K1State n
  | 1 => lowZeroCoefficientsP5J0I4K2State n
  | 2 => lowZeroCoefficientsP5J0I4K3State n
  | 3 => lowZeroCoefficientsP5J0I4K4State n
  | 4 => lowZeroCoefficientsP5J0I4K5State n
  | _ => (0,0)

theorem lowZeroPanelP5J0I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J0I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J0I4K1Point)
        (theta48PanelCenter 0 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J0I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I4Coefficient,lowZeroSeedP5J0I4K1Point,lowZeroSeedP5J0I4K1Point]
  · convert lowZeroCoefficientsP5J0I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I4Coefficient,lowZeroSeedP5J0I4K1Point,lowZeroSeedP5J0I4K2Point]
  · convert lowZeroCoefficientsP5J0I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I4Coefficient,lowZeroSeedP5J0I4K1Point,lowZeroSeedP5J0I4K3Point]
  · convert lowZeroCoefficientsP5J0I4K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I4Coefficient,lowZeroSeedP5J0I4K1Point,lowZeroSeedP5J0I4K4Point]
  · convert lowZeroCoefficientsP5J0I4K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I4Coefficient,lowZeroSeedP5J0I4K1Point,lowZeroSeedP5J0I4K5Point]

def lowZeroPanelP5J0I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP5J0I4Coefficient

theorem lowZeroPanelP5J0I4Value_eq : lowZeroPanelP5J0I4Value=(2464823316206594848569533064877224602068913249703485593500881852146997255061909290618302870182385636703409116019695769522868291498762983090495626002528215761735936664435712322975915134271:ℚ)/2621383943391470234031324543000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J0I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J0I4K1Point (theta48PanelCenter 0 4)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP5J0I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J0I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J0I4K1Point (theta48PanelCenter 0 4)
    ((1:ℚ)/16) lowZeroPanelP5J0I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J0I4Value,theta48PanelHalfWidth]

end ReciprocalXi
