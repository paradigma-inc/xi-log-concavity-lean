import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I1K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I1K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I1K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J0I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J0I1K1State n
  | 1 => lowZeroCoefficientsP0J0I1K2State n
  | 2 => lowZeroCoefficientsP0J0I1K3State n
  | 3 => lowZeroCoefficientsP0J0I1K4State n
  | 4 => lowZeroCoefficientsP0J0I1K5State n
  | _ => (0,0)

theorem lowZeroPanelP0J0I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J0I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J0I1K1Point)
        (theta48PanelCenter 0 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J0I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I1Coefficient,lowZeroSeedP0J0I1K1Point,lowZeroSeedP0J0I1K1Point]
  · convert lowZeroCoefficientsP0J0I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I1Coefficient,lowZeroSeedP0J0I1K1Point,lowZeroSeedP0J0I1K2Point]
  · convert lowZeroCoefficientsP0J0I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I1Coefficient,lowZeroSeedP0J0I1K1Point,lowZeroSeedP0J0I1K3Point]
  · convert lowZeroCoefficientsP0J0I1K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I1Coefficient,lowZeroSeedP0J0I1K1Point,lowZeroSeedP0J0I1K4Point]
  · convert lowZeroCoefficientsP0J0I1K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I1Coefficient,lowZeroSeedP0J0I1K1Point,lowZeroSeedP0J0I1K5Point]

def lowZeroPanelP0J0I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP0J0I1Coefficient

theorem lowZeroPanelP0J0I1Value_eq : lowZeroPanelP0J0I1Value=(39965960652120037110982577596080501237406075865304375812608847167800537380622562923148199549741556472777568601392054034518353606298192412020052694005135026611864132196537085457852373518574299:ℚ)/20271162034246239319764232691019000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J0I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J0I1K1Point (theta48PanelCenter 0 1)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP0J0I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J0I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J0I1K1Point (theta48PanelCenter 0 1)
    ((1:ℚ)/16) lowZeroPanelP0J0I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J0I1Value,theta48PanelHalfWidth]

end ReciprocalXi
