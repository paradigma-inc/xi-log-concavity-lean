import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I4K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I4K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I4K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J0I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J0I4K1State n
  | 1 => lowZeroCoefficientsP3J0I4K2State n
  | 2 => lowZeroCoefficientsP3J0I4K3State n
  | 3 => lowZeroCoefficientsP3J0I4K4State n
  | 4 => lowZeroCoefficientsP3J0I4K5State n
  | _ => (0,0)

theorem lowZeroPanelP3J0I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J0I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J0I4K1Point)
        (theta48PanelCenter 0 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J0I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I4Coefficient,lowZeroSeedP3J0I4K1Point,lowZeroSeedP3J0I4K1Point]
  · convert lowZeroCoefficientsP3J0I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I4Coefficient,lowZeroSeedP3J0I4K1Point,lowZeroSeedP3J0I4K2Point]
  · convert lowZeroCoefficientsP3J0I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I4Coefficient,lowZeroSeedP3J0I4K1Point,lowZeroSeedP3J0I4K3Point]
  · convert lowZeroCoefficientsP3J0I4K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I4Coefficient,lowZeroSeedP3J0I4K1Point,lowZeroSeedP3J0I4K4Point]
  · convert lowZeroCoefficientsP3J0I4K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I4Coefficient,lowZeroSeedP3J0I4K1Point,lowZeroSeedP3J0I4K5Point]

def lowZeroPanelP3J0I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP3J0I4Coefficient

theorem lowZeroPanelP3J0I4Value_eq : lowZeroPanelP3J0I4Value=(-163698919637867500262812468010570124631648901205301730109854255924820074579315847991441346427897403914881801833661795898639588064784020933528036878782100307376158733811522752905196482810199:ℚ)/2252351337138471035529359187891000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J0I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J0I4K1Point (theta48PanelCenter 0 4)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP3J0I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J0I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J0I4K1Point (theta48PanelCenter 0 4)
    ((1:ℚ)/16) lowZeroPanelP3J0I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J0I4Value,theta48PanelHalfWidth]

end ReciprocalXi
