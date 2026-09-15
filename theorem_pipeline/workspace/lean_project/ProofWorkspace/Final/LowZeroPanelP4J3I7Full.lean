import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J3I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J3I7K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J3I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J3I7K1State n
  | 1 => lowZeroCoefficientsP4J3I7K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J3I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J3I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J3I7K1Point)
        (theta48PanelCenter 3 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J3I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J3I7Coefficient,lowZeroSeedP4J3I7K1Point,lowZeroSeedP4J3I7K1Point]
  · convert lowZeroCoefficientsP4J3I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J3I7Coefficient,lowZeroSeedP4J3I7K1Point,lowZeroSeedP4J3I7K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP4J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP4J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP4J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I7Coefficient]

def lowZeroPanelP4J3I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP4J3I7Coefficient

theorem lowZeroPanelP4J3I7Value_eq : lowZeroPanelP4J3I7Value=(-59865804288766404434645435703947629297040739017022757973000410619916913974163948625297184863568963456840408211325382903559881103264663627766539111746081545907889133059801:ℚ)/253389525428077991497052908637737500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J3I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J3I7K1Point (theta48PanelCenter 3 7)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP4J3I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J3I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J3I7K1Point (theta48PanelCenter 3 7)
    ((1:ℚ)/2) lowZeroPanelP4J3I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J3I7Value,theta48PanelHalfWidth]

end ReciprocalXi
