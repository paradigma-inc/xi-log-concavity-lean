import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I5K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I5K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I5K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I5K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I5K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J0I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J0I5K1State n
  | 1 => lowZeroCoefficientsP0J0I5K2State n
  | 2 => lowZeroCoefficientsP0J0I5K3State n
  | 3 => lowZeroCoefficientsP0J0I5K4State n
  | 4 => lowZeroCoefficientsP0J0I5K5State n
  | _ => (0,0)

theorem lowZeroPanelP0J0I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J0I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J0I5K1Point)
        (theta48PanelCenter 0 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J0I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I5Coefficient,lowZeroSeedP0J0I5K1Point,lowZeroSeedP0J0I5K1Point]
  · convert lowZeroCoefficientsP0J0I5K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I5Coefficient,lowZeroSeedP0J0I5K1Point,lowZeroSeedP0J0I5K2Point]
  · convert lowZeroCoefficientsP0J0I5K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I5Coefficient,lowZeroSeedP0J0I5K1Point,lowZeroSeedP0J0I5K3Point]
  · convert lowZeroCoefficientsP0J0I5K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I5Coefficient,lowZeroSeedP0J0I5K1Point,lowZeroSeedP0J0I5K4Point]
  · convert lowZeroCoefficientsP0J0I5K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I5Coefficient,lowZeroSeedP0J0I5K1Point,lowZeroSeedP0J0I5K5Point]

def lowZeroPanelP0J0I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP0J0I5Coefficient

theorem lowZeroPanelP0J0I5Value_eq : lowZeroPanelP0J0I5Value=(-860808045251852456033466475252977243478553371830237773757052754878050464184700871093817322173769214582242983577258784534673795298603861176428507313984947339306844530384669591663433890240767:ℚ)/1192421296132131724692013687707000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J0I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J0I5K1Point (theta48PanelCenter 0 5)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP0J0I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J0I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J0I5K1Point (theta48PanelCenter 0 5)
    ((1:ℚ)/16) lowZeroPanelP0J0I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J0I5Value,theta48PanelHalfWidth]

end ReciprocalXi
