import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I4K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I4K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I4K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J0I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J0I4K1State n
  | 1 => lowZeroCoefficientsP1J0I4K2State n
  | 2 => lowZeroCoefficientsP1J0I4K3State n
  | 3 => lowZeroCoefficientsP1J0I4K4State n
  | 4 => lowZeroCoefficientsP1J0I4K5State n
  | _ => (0,0)

theorem lowZeroPanelP1J0I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J0I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J0I4K1Point)
        (theta48PanelCenter 0 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J0I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I4Coefficient,lowZeroSeedP1J0I4K1Point,lowZeroSeedP1J0I4K1Point]
  · convert lowZeroCoefficientsP1J0I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I4Coefficient,lowZeroSeedP1J0I4K1Point,lowZeroSeedP1J0I4K2Point]
  · convert lowZeroCoefficientsP1J0I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I4Coefficient,lowZeroSeedP1J0I4K1Point,lowZeroSeedP1J0I4K3Point]
  · convert lowZeroCoefficientsP1J0I4K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I4Coefficient,lowZeroSeedP1J0I4K1Point,lowZeroSeedP1J0I4K4Point]
  · convert lowZeroCoefficientsP1J0I4K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I4Coefficient,lowZeroSeedP1J0I4K1Point,lowZeroSeedP1J0I4K5Point]

def lowZeroPanelP1J0I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP1J0I4Coefficient

theorem lowZeroPanelP1J0I4Value_eq : lowZeroPanelP1J0I4Value=(-2422300738734695743852264845152598964766980267248941354674975692062970795898840844073097666031495711112156763587071421098843911346673065627431270779711317328380169249683057885731857335362529:ℚ)/1842832912204203574524021153729000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J0I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J0I4K1Point (theta48PanelCenter 0 4)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP1J0I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J0I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J0I4K1Point (theta48PanelCenter 0 4)
    ((1:ℚ)/16) lowZeroPanelP1J0I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J0I4Value,theta48PanelHalfWidth]

end ReciprocalXi
