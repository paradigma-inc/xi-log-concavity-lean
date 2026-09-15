import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I5K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I5K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I5K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I5K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J1I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J1I5K1State n
  | 1 => lowZeroCoefficientsP2J1I5K2State n
  | 2 => lowZeroCoefficientsP2J1I5K3State n
  | 3 => lowZeroCoefficientsP2J1I5K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J1I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J1I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J1I5K1Point)
        (theta48PanelCenter 1 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J1I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I5Coefficient,lowZeroSeedP2J1I5K1Point,lowZeroSeedP2J1I5K1Point]
  · convert lowZeroCoefficientsP2J1I5K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I5Coefficient,lowZeroSeedP2J1I5K1Point,lowZeroSeedP2J1I5K2Point]
  · convert lowZeroCoefficientsP2J1I5K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I5Coefficient,lowZeroSeedP2J1I5K1Point,lowZeroSeedP2J1I5K3Point]
  · convert lowZeroCoefficientsP2J1I5K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I5Coefficient,lowZeroSeedP2J1I5K1Point,lowZeroSeedP2J1I5K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J1I5K1Point
        (theta48PanelCenter 1 5) (theta48PanelHalfWidth 1) 5 n
        (by norm_num [lowZeroSeedP2J1I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J1I5Coefficient]

def lowZeroPanelP2J1I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP2J1I5Coefficient

theorem lowZeroPanelP2J1I5Value_eq : lowZeroPanelP2J1I5Value=(71632013260591707640078323743775069990674684276335988130029435721828324506969205618651492091341537790453806242570340346920596199166281745762364045121313943048609359947920262902860777513:ℚ)/14479401453033028085545880493585000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J1I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J1I5K1Point (theta48PanelCenter 1 5)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP2J1I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J1I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J1I5K1Point (theta48PanelCenter 1 5)
    ((1:ℚ)/8) lowZeroPanelP2J1I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J1I5Value,theta48PanelHalfWidth]

end ReciprocalXi
