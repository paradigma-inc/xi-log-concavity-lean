import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I1K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I1K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I1K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J0I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J0I1K1State n
  | 1 => lowZeroCoefficientsP3J0I1K2State n
  | 2 => lowZeroCoefficientsP3J0I1K3State n
  | 3 => lowZeroCoefficientsP3J0I1K4State n
  | 4 => lowZeroCoefficientsP3J0I1K5State n
  | _ => (0,0)

theorem lowZeroPanelP3J0I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J0I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J0I1K1Point)
        (theta48PanelCenter 0 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J0I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I1Coefficient,lowZeroSeedP3J0I1K1Point,lowZeroSeedP3J0I1K1Point]
  · convert lowZeroCoefficientsP3J0I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I1Coefficient,lowZeroSeedP3J0I1K1Point,lowZeroSeedP3J0I1K2Point]
  · convert lowZeroCoefficientsP3J0I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I1Coefficient,lowZeroSeedP3J0I1K1Point,lowZeroSeedP3J0I1K3Point]
  · convert lowZeroCoefficientsP3J0I1K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I1Coefficient,lowZeroSeedP3J0I1K1Point,lowZeroSeedP3J0I1K4Point]
  · convert lowZeroCoefficientsP3J0I1K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I1Coefficient,lowZeroSeedP3J0I1K1Point,lowZeroSeedP3J0I1K5Point]

def lowZeroPanelP3J0I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP3J0I1Coefficient

theorem lowZeroPanelP3J0I1Value_eq : lowZeroPanelP3J0I1Value=(-19005818611270819674253286137325314074875739932251130158132803740438772789756913061502779733237074640254979924951236602710671707144871637347262349361268617387477785209836937978326084722070569:ℚ)/20271162034246239319764232691019000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J0I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J0I1K1Point (theta48PanelCenter 0 1)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP3J0I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J0I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J0I1K1Point (theta48PanelCenter 0 1)
    ((1:ℚ)/16) lowZeroPanelP3J0I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J0I1Value,theta48PanelHalfWidth]

end ReciprocalXi
