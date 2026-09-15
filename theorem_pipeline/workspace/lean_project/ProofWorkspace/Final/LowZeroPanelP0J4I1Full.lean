import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J4I1K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J4I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J4I1K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP0J4I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J4I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J4I1K1Point)
        (theta48PanelCenter 4 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J4I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J4I1Coefficient,lowZeroSeedP0J4I1K1Point,lowZeroSeedP0J4I1K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J4I1K1Point
        (theta48PanelCenter 4 1) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP0J4I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J4I1Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J4I1K1Point
        (theta48PanelCenter 4 1) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP0J4I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J4I1Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J4I1K1Point
        (theta48PanelCenter 4 1) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP0J4I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J4I1Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J4I1K1Point
        (theta48PanelCenter 4 1) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP0J4I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J4I1Coefficient]

def lowZeroPanelP0J4I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP0J4I1Coefficient

theorem lowZeroPanelP0J4I1Value_eq : lowZeroPanelP0J4I1Value=(-243101606021654740267834938430816798906280603421962078986924109540756763846642168787032953808503543659715572208377188352268289087200030368410268247040067732668863:ℚ)/97773393049883466390281258156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J4I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J4I1K1Point (theta48PanelCenter 4 1)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP0J4I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J4I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J4I1K1Point (theta48PanelCenter 4 1)
    ((1:ℚ)/1) lowZeroPanelP0J4I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J4I1Value,theta48PanelHalfWidth]

end ReciprocalXi
