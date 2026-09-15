import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J2I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J2I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J2I4K3Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J2I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J2I4K1State n
  | 1 => lowZeroCoefficientsP3J2I4K2State n
  | 2 => lowZeroCoefficientsP3J2I4K3State n
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J2I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J2I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J2I4K1Point)
        (theta48PanelCenter 2 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J2I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J2I4Coefficient,lowZeroSeedP3J2I4K1Point,lowZeroSeedP3J2I4K1Point]
  · convert lowZeroCoefficientsP3J2I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J2I4Coefficient,lowZeroSeedP3J2I4K1Point,lowZeroSeedP3J2I4K2Point]
  · convert lowZeroCoefficientsP3J2I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J2I4Coefficient,lowZeroSeedP3J2I4K1Point,lowZeroSeedP3J2I4K3Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J2I4K1Point
        (theta48PanelCenter 2 4) (theta48PanelHalfWidth 2) 4 n
        (by norm_num [lowZeroSeedP3J2I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J2I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J2I4K1Point
        (theta48PanelCenter 2 4) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP3J2I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J2I4Coefficient]

def lowZeroPanelP3J2I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP3J2I4Coefficient

theorem lowZeroPanelP3J2I4Value_eq : lowZeroPanelP3J2I4Value=(9975437613860602732401413900757598629736964990483010900207790817952232200033338786409632388296221785333543853456288173894763308039072398706107455758667625665630318773368105543795969:ℚ)/12797450779195858156416813567562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J2I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J2I4K1Point (theta48PanelCenter 2 4)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP3J2I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J2I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J2I4K1Point (theta48PanelCenter 2 4)
    ((1:ℚ)/4) lowZeroPanelP3J2I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J2I4Value,theta48PanelHalfWidth]

end ReciprocalXi
