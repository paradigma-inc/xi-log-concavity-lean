import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J3I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J3I7K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J3I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J3I7K1State n
  | 1 => lowZeroCoefficientsP0J3I7K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP0J3I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J3I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J3I7K1Point)
        (theta48PanelCenter 3 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J3I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J3I7Coefficient,lowZeroSeedP0J3I7K1Point,lowZeroSeedP0J3I7K1Point]
  · convert lowZeroCoefficientsP0J3I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J3I7Coefficient,lowZeroSeedP0J3I7K1Point,lowZeroSeedP0J3I7K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP0J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J3I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP0J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J3I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP0J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J3I7Coefficient]

def lowZeroPanelP0J3I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP0J3I7Coefficient

theorem lowZeroPanelP0J3I7Value_eq : lowZeroPanelP0J3I7Value=(77800732973279728628736106033518011779729788235246073061198059330604225260234449223779620442028761645252172726050805424652130873584911552028169641188354742333526894363669:ℚ)/316736906785097489371316135797171875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J3I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J3I7K1Point (theta48PanelCenter 3 7)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP0J3I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J3I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J3I7K1Point (theta48PanelCenter 3 7)
    ((1:ℚ)/2) lowZeroPanelP0J3I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J3I7Value,theta48PanelHalfWidth]

end ReciprocalXi
