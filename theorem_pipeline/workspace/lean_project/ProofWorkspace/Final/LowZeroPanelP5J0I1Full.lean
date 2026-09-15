import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I1K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I1K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J0I1K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J0I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J0I1K1State n
  | 1 => lowZeroCoefficientsP5J0I1K2State n
  | 2 => lowZeroCoefficientsP5J0I1K3State n
  | 3 => lowZeroCoefficientsP5J0I1K4State n
  | 4 => lowZeroCoefficientsP5J0I1K5State n
  | _ => (0,0)

theorem lowZeroPanelP5J0I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J0I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J0I1K1Point)
        (theta48PanelCenter 0 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J0I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I1Coefficient,lowZeroSeedP5J0I1K1Point,lowZeroSeedP5J0I1K1Point]
  · convert lowZeroCoefficientsP5J0I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I1Coefficient,lowZeroSeedP5J0I1K1Point,lowZeroSeedP5J0I1K2Point]
  · convert lowZeroCoefficientsP5J0I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I1Coefficient,lowZeroSeedP5J0I1K1Point,lowZeroSeedP5J0I1K3Point]
  · convert lowZeroCoefficientsP5J0I1K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I1Coefficient,lowZeroSeedP5J0I1K1Point,lowZeroSeedP5J0I1K4Point]
  · convert lowZeroCoefficientsP5J0I1K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J0I1Coefficient,lowZeroSeedP5J0I1K1Point,lowZeroSeedP5J0I1K5Point]

def lowZeroPanelP5J0I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP5J0I1Coefficient

theorem lowZeroPanelP5J0I1Value_eq : lowZeroPanelP5J0I1Value=(-80316591300049492905250404055753370371993540008693698677910501496676742558554354407388444867761332208938085919793076292382918166979073529573662644535310781737012759278119867153655260889203:ℚ)/32695422635881031160910052727450000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J0I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J0I1K1Point (theta48PanelCenter 0 1)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP5J0I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J0I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J0I1K1Point (theta48PanelCenter 0 1)
    ((1:ℚ)/16) lowZeroPanelP5J0I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J0I1Value,theta48PanelHalfWidth]

end ReciprocalXi
