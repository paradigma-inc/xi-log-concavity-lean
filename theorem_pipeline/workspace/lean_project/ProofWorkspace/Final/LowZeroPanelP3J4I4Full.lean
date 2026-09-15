import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J4I4K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J4I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J4I4K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J4I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J4I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J4I4K1Point)
        (theta48PanelCenter 4 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J4I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J4I4Coefficient,lowZeroSeedP3J4I4K1Point,lowZeroSeedP3J4I4K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP3J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP3J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP3J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP3J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I4Coefficient]

def lowZeroPanelP3J4I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP3J4I4Coefficient

theorem lowZeroPanelP3J4I4Value_eq : lowZeroPanelP3J4I4Value=(-96204429196311545291659572040053646789273978723409222316632752714631365321037275147530850298087081569186376535286731756809316007547944756009883773707289799:ℚ)/1771954723273272667811558801662500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J4I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J4I4K1Point (theta48PanelCenter 4 4)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP3J4I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J4I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J4I4K1Point (theta48PanelCenter 4 4)
    ((1:ℚ)/1) lowZeroPanelP3J4I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J4I4Value,theta48PanelHalfWidth]

end ReciprocalXi
