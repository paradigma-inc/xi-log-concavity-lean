import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J3I6K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J3I6K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J3I6Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J3I6K1State n
  | 1 => lowZeroCoefficientsP1J3I6K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP1J3I6_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J3I6Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J3I6K1Point)
        (theta48PanelCenter 3 6:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J3I6K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J3I6Coefficient,lowZeroSeedP1J3I6K1Point,lowZeroSeedP1J3I6K1Point]
  · convert lowZeroCoefficientsP1J3I6K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J3I6Coefficient,lowZeroSeedP1J3I6K1Point,lowZeroSeedP1J3I6K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I6K1Point
        (theta48PanelCenter 3 6) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP1J3I6K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I6Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I6K1Point
        (theta48PanelCenter 3 6) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP1J3I6K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I6Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I6K1Point
        (theta48PanelCenter 3 6) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP1J3I6K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I6Coefficient]

def lowZeroPanelP1J3I6Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP1J3I6Coefficient

theorem lowZeroPanelP1J3I6Value_eq : lowZeroPanelP1J3I6Value=(57320154646131926749181181813738185094698788002644975590286617813606974869401814871475052148153637522572339660430500926094891594067283812199206820054334920446985698434413:ℚ)/8798247410697152482536559327699218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J3I6_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J3I6K1Point (theta48PanelCenter 3 6)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP1J3I6Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J3I6_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J3I6K1Point (theta48PanelCenter 3 6)
    ((1:ℚ)/2) lowZeroPanelP1J3I6Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J3I6Value,theta48PanelHalfWidth]

end ReciprocalXi
