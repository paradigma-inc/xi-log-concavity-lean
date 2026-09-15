import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I5K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I5K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I5K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I5K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I5K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J0I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J0I5K1State n
  | 1 => lowZeroCoefficientsP3J0I5K2State n
  | 2 => lowZeroCoefficientsP3J0I5K3State n
  | 3 => lowZeroCoefficientsP3J0I5K4State n
  | 4 => lowZeroCoefficientsP3J0I5K5State n
  | _ => (0,0)

theorem lowZeroPanelP3J0I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J0I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J0I5K1Point)
        (theta48PanelCenter 0 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J0I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I5Coefficient,lowZeroSeedP3J0I5K1Point,lowZeroSeedP3J0I5K1Point]
  · convert lowZeroCoefficientsP3J0I5K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I5Coefficient,lowZeroSeedP3J0I5K1Point,lowZeroSeedP3J0I5K2Point]
  · convert lowZeroCoefficientsP3J0I5K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I5Coefficient,lowZeroSeedP3J0I5K1Point,lowZeroSeedP3J0I5K3Point]
  · convert lowZeroCoefficientsP3J0I5K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I5Coefficient,lowZeroSeedP3J0I5K1Point,lowZeroSeedP3J0I5K4Point]
  · convert lowZeroCoefficientsP3J0I5K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I5Coefficient,lowZeroSeedP3J0I5K1Point,lowZeroSeedP3J0I5K5Point]

def lowZeroPanelP3J0I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP3J0I5Coefficient

theorem lowZeroPanelP3J0I5Value_eq : lowZeroPanelP3J0I5Value=(3836081489686241067074343029985049860366611663685047505510579578147783602434229791163795370245152385109479688817818662276164191094956375132989725537853273698754847866236617673552931246971037:ℚ)/6757054011415413106588077563673000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J0I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J0I5K1Point (theta48PanelCenter 0 5)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP3J0I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J0I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J0I5K1Point (theta48PanelCenter 0 5)
    ((1:ℚ)/16) lowZeroPanelP3J0I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J0I5Value,theta48PanelHalfWidth]

end ReciprocalXi
