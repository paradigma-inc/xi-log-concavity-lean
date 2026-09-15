import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I6K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I6K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I6K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I6K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I6K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J0I6Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J0I6K1State n
  | 1 => lowZeroCoefficientsP3J0I6K2State n
  | 2 => lowZeroCoefficientsP3J0I6K3State n
  | 3 => lowZeroCoefficientsP3J0I6K4State n
  | 4 => lowZeroCoefficientsP3J0I6K5State n
  | _ => (0,0)

theorem lowZeroPanelP3J0I6_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J0I6Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J0I6K1Point)
        (theta48PanelCenter 0 6:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J0I6K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I6Coefficient,lowZeroSeedP3J0I6K1Point,lowZeroSeedP3J0I6K1Point]
  · convert lowZeroCoefficientsP3J0I6K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I6Coefficient,lowZeroSeedP3J0I6K1Point,lowZeroSeedP3J0I6K2Point]
  · convert lowZeroCoefficientsP3J0I6K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I6Coefficient,lowZeroSeedP3J0I6K1Point,lowZeroSeedP3J0I6K3Point]
  · convert lowZeroCoefficientsP3J0I6K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I6Coefficient,lowZeroSeedP3J0I6K1Point,lowZeroSeedP3J0I6K4Point]
  · convert lowZeroCoefficientsP3J0I6K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I6Coefficient,lowZeroSeedP3J0I6K1Point,lowZeroSeedP3J0I6K5Point]

def lowZeroPanelP3J0I6Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP3J0I6Coefficient

theorem lowZeroPanelP3J0I6Value_eq : lowZeroPanelP3J0I6Value=(10752609923508255072335608797085223842234410668041931710240422147105152609536987273410206861105345635771129651797613775083801435546675952535443161939509646289104042097014586919961096126424557:ℚ)/20271162034246239319764232691019000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J0I6_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J0I6K1Point (theta48PanelCenter 0 6)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP3J0I6Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J0I6_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J0I6K1Point (theta48PanelCenter 0 6)
    ((1:ℚ)/16) lowZeroPanelP3J0I6Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J0I6Value,theta48PanelHalfWidth]

end ReciprocalXi
