import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J3I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J3I7K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J3I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J3I7K1State n
  | 1 => lowZeroCoefficientsP3J3I7K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J3I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J3I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J3I7K1Point)
        (theta48PanelCenter 3 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J3I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J3I7Coefficient,lowZeroSeedP3J3I7K1Point,lowZeroSeedP3J3I7K1Point]
  · convert lowZeroCoefficientsP3J3I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J3I7Coefficient,lowZeroSeedP3J3I7K1Point,lowZeroSeedP3J3I7K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP3J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP3J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP3J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I7Coefficient]

def lowZeroPanelP3J3I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP3J3I7Coefficient

theorem lowZeroPanelP3J3I7Value_eq : lowZeroPanelP3J3I7Value=(-628178548018799849571118479274886086296092296720351224927184165143760739760884862991351063443461667322775750686886568687090076277035984236942441689275824726021118905386963:ℚ)/2533895254280779914970529086377375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J3I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J3I7K1Point (theta48PanelCenter 3 7)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP3J3I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J3I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J3I7K1Point (theta48PanelCenter 3 7)
    ((1:ℚ)/2) lowZeroPanelP3J3I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J3I7Value,theta48PanelHalfWidth]

end ReciprocalXi
