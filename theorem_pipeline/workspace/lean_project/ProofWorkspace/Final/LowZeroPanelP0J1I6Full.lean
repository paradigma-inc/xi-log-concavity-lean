import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I6K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I6K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I6K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I6K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J1I6Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J1I6K1State n
  | 1 => lowZeroCoefficientsP0J1I6K2State n
  | 2 => lowZeroCoefficientsP0J1I6K3State n
  | 3 => lowZeroCoefficientsP0J1I6K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP0J1I6_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J1I6Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J1I6K1Point)
        (theta48PanelCenter 1 6:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J1I6K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I6Coefficient,lowZeroSeedP0J1I6K1Point,lowZeroSeedP0J1I6K1Point]
  · convert lowZeroCoefficientsP0J1I6K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I6Coefficient,lowZeroSeedP0J1I6K1Point,lowZeroSeedP0J1I6K2Point]
  · convert lowZeroCoefficientsP0J1I6K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I6Coefficient,lowZeroSeedP0J1I6K1Point,lowZeroSeedP0J1I6K3Point]
  · convert lowZeroCoefficientsP0J1I6K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I6Coefficient,lowZeroSeedP0J1I6K1Point,lowZeroSeedP0J1I6K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J1I6K1Point
        (theta48PanelCenter 1 6) (theta48PanelHalfWidth 1) 5 n
        (by norm_num [lowZeroSeedP0J1I6K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J1I6Coefficient]

def lowZeroPanelP0J1I6Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP0J1I6Coefficient

theorem lowZeroPanelP0J1I6Value_eq : lowZeroPanelP0J1I6Value=(-217378193335300858355020938893805799121305070557224113186933339552112293326009933470971093153680837969530983880527739819705276268789944656422977487499051285722411450349822398153912567399:ℚ)/105578968928365829790438711932390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J1I6_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J1I6K1Point (theta48PanelCenter 1 6)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP0J1I6Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J1I6_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J1I6K1Point (theta48PanelCenter 1 6)
    ((1:ℚ)/8) lowZeroPanelP0J1I6Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J1I6Value,theta48PanelHalfWidth]

end ReciprocalXi
