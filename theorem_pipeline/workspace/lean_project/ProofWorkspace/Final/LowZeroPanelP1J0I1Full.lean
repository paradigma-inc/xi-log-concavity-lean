import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I1K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I1K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I1K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J0I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J0I1K1State n
  | 1 => lowZeroCoefficientsP1J0I1K2State n
  | 2 => lowZeroCoefficientsP1J0I1K3State n
  | 3 => lowZeroCoefficientsP1J0I1K4State n
  | 4 => lowZeroCoefficientsP1J0I1K5State n
  | _ => (0,0)

theorem lowZeroPanelP1J0I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J0I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J0I1K1Point)
        (theta48PanelCenter 0 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J0I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I1Coefficient,lowZeroSeedP1J0I1K1Point,lowZeroSeedP1J0I1K1Point]
  · convert lowZeroCoefficientsP1J0I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I1Coefficient,lowZeroSeedP1J0I1K1Point,lowZeroSeedP1J0I1K2Point]
  · convert lowZeroCoefficientsP1J0I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I1Coefficient,lowZeroSeedP1J0I1K1Point,lowZeroSeedP1J0I1K3Point]
  · convert lowZeroCoefficientsP1J0I1K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I1Coefficient,lowZeroSeedP1J0I1K1Point,lowZeroSeedP1J0I1K4Point]
  · convert lowZeroCoefficientsP1J0I1K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I1Coefficient,lowZeroSeedP1J0I1K1Point,lowZeroSeedP1J0I1K5Point]

def lowZeroPanelP1J0I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP1J0I1Coefficient

theorem lowZeroPanelP1J0I1Value_eq : lowZeroPanelP1J0I1Value=(3633269150192730646452961599628623123440139935511274821991643240269536960409650434353858492728408201114349824235437244189072996162449286092798676543518560209320122546744552039856628161183101:ℚ)/1842832912204203574524021153729000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J0I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J0I1K1Point (theta48PanelCenter 0 1)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP1J0I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J0I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J0I1K1Point (theta48PanelCenter 0 1)
    ((1:ℚ)/16) lowZeroPanelP1J0I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J0I1Value,theta48PanelHalfWidth]

end ReciprocalXi
