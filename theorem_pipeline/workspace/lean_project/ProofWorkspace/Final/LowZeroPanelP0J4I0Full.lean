import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J4I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J4I0K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J4I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J4I0K1State n
  | 1 => lowZeroCoefficientsP0J4I0K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP0J4I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J4I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J4I0K1Point)
        (theta48PanelCenter 4 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J4I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J4I0Coefficient,lowZeroSeedP0J4I0K1Point,lowZeroSeedP0J4I0K1Point]
  · convert lowZeroCoefficientsP0J4I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J4I0Coefficient,lowZeroSeedP0J4I0K1Point,lowZeroSeedP0J4I0K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J4I0K1Point
        (theta48PanelCenter 4 0) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP0J4I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J4I0Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J4I0K1Point
        (theta48PanelCenter 4 0) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP0J4I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J4I0Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J4I0K1Point
        (theta48PanelCenter 4 0) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP0J4I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J4I0Coefficient]

def lowZeroPanelP0J4I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP0J4I0Coefficient

theorem lowZeroPanelP0J4I0Value_eq : lowZeroPanelP0J4I0Value=(9278134779819093170377021033641454904562940079814874297405337830666804473710683531562019988139638590116301078233792651394243643153580435194652241485522455372120556398697:ℚ)/1266947627140389957485264543188687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J4I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J4I0K1Point (theta48PanelCenter 4 0)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP0J4I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J4I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J4I0K1Point (theta48PanelCenter 4 0)
    ((1:ℚ)/1) lowZeroPanelP0J4I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J4I0Value,theta48PanelHalfWidth]

end ReciprocalXi
