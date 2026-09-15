import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I4K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I4K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I4K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J0I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J0I4K1State n
  | 1 => lowZeroCoefficientsP0J0I4K2State n
  | 2 => lowZeroCoefficientsP0J0I4K3State n
  | 3 => lowZeroCoefficientsP0J0I4K4State n
  | 4 => lowZeroCoefficientsP0J0I4K5State n
  | _ => (0,0)

theorem lowZeroPanelP0J0I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J0I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J0I4K1Point)
        (theta48PanelCenter 0 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J0I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I4Coefficient,lowZeroSeedP0J0I4K1Point,lowZeroSeedP0J0I4K1Point]
  · convert lowZeroCoefficientsP0J0I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I4Coefficient,lowZeroSeedP0J0I4K1Point,lowZeroSeedP0J0I4K2Point]
  · convert lowZeroCoefficientsP0J0I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I4Coefficient,lowZeroSeedP0J0I4K1Point,lowZeroSeedP0J0I4K3Point]
  · convert lowZeroCoefficientsP0J0I4K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I4Coefficient,lowZeroSeedP0J0I4K1Point,lowZeroSeedP0J0I4K4Point]
  · convert lowZeroCoefficientsP0J0I4K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I4Coefficient,lowZeroSeedP0J0I4K1Point,lowZeroSeedP0J0I4K5Point]

def lowZeroPanelP0J0I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP0J0I4Coefficient

theorem lowZeroPanelP0J0I4Value_eq : lowZeroPanelP0J0I4Value=(-26645308126081653182374913296678318890514738203209967076677902462454843864630526385155932930562015069376503950700222925471738869754893609127723629918682914933046159943414300816373390090883123:ℚ)/20271162034246239319764232691019000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J0I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J0I4K1Point (theta48PanelCenter 0 4)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP0J0I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J0I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J0I4K1Point (theta48PanelCenter 0 4)
    ((1:ℚ)/16) lowZeroPanelP0J0I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J0I4Value,theta48PanelHalfWidth]

end ReciprocalXi
