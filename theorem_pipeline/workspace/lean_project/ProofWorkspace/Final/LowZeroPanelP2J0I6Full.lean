import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I6K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I6K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I6K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I6K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J0I6K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J0I6Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J0I6K1State n
  | 1 => lowZeroCoefficientsP2J0I6K2State n
  | 2 => lowZeroCoefficientsP2J0I6K3State n
  | 3 => lowZeroCoefficientsP2J0I6K4State n
  | 4 => lowZeroCoefficientsP2J0I6K5State n
  | _ => (0,0)

theorem lowZeroPanelP2J0I6_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J0I6Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J0I6K1Point)
        (theta48PanelCenter 0 6:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J0I6K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I6Coefficient,lowZeroSeedP2J0I6K1Point,lowZeroSeedP2J0I6K1Point]
  · convert lowZeroCoefficientsP2J0I6K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I6Coefficient,lowZeroSeedP2J0I6K1Point,lowZeroSeedP2J0I6K2Point]
  · convert lowZeroCoefficientsP2J0I6K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I6Coefficient,lowZeroSeedP2J0I6K1Point,lowZeroSeedP2J0I6K3Point]
  · convert lowZeroCoefficientsP2J0I6K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I6Coefficient,lowZeroSeedP2J0I6K1Point,lowZeroSeedP2J0I6K4Point]
  · convert lowZeroCoefficientsP2J0I6K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J0I6Coefficient,lowZeroSeedP2J0I6K1Point,lowZeroSeedP2J0I6K5Point]

def lowZeroPanelP2J0I6Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP2J0I6Coefficient

theorem lowZeroPanelP2J0I6Value_eq : lowZeroPanelP2J0I6Value=(358420330783608502411186959902725595892710785500314061682751655373562022389885018698157611915511744594789727717695965995492734701706835752119112327339047833430209382281359269974148782496493:ℚ)/675705401141541310658807756367300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J0I6_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J0I6K1Point (theta48PanelCenter 0 6)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP2J0I6Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J0I6_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J0I6K1Point (theta48PanelCenter 0 6)
    ((1:ℚ)/16) lowZeroPanelP2J0I6Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J0I6Value,theta48PanelHalfWidth]

end ReciprocalXi
