import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I5K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I5K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I5K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I5K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I5K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J0I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J0I5K1State n
  | 1 => lowZeroCoefficientsP2J0I5K2State n
  | 2 => lowZeroCoefficientsP2J0I5K3State n
  | 3 => lowZeroCoefficientsP2J0I5K4State n
  | 4 => lowZeroCoefficientsP2J0I5K5State n
  | _ => (0,0)

theorem lowZeroPanelP2J0I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J0I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J0I5K1Point)
        (theta48PanelCenter 0 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J0I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I5Coefficient,lowZeroSeedP2J0I5K1Point,lowZeroSeedP2J0I5K1Point]
  · convert lowZeroCoefficientsP2J0I5K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I5Coefficient,lowZeroSeedP2J0I5K1Point,lowZeroSeedP2J0I5K2Point]
  · convert lowZeroCoefficientsP2J0I5K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I5Coefficient,lowZeroSeedP2J0I5K1Point,lowZeroSeedP2J0I5K3Point]
  · convert lowZeroCoefficientsP2J0I5K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I5Coefficient,lowZeroSeedP2J0I5K1Point,lowZeroSeedP2J0I5K4Point]
  · convert lowZeroCoefficientsP2J0I5K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I5Coefficient,lowZeroSeedP2J0I5K1Point,lowZeroSeedP2J0I5K5Point]

def lowZeroPanelP2J0I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP2J0I5Coefficient

theorem lowZeroPanelP2J0I5Value_eq : lowZeroPanelP2J0I5Value=(719265279316170200076439318118261807762009452637619528555696392150167412957356842484707748861909938272561829722582693293929401490298555242631056375477981594855565782123377233779168712368059:ℚ)/1266947627140389957485264543188687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J0I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J0I5K1Point (theta48PanelCenter 0 5)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP2J0I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J0I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J0I5K1Point (theta48PanelCenter 0 5)
    ((1:ℚ)/16) lowZeroPanelP2J0I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J0I5Value,theta48PanelHalfWidth]

end ReciprocalXi
