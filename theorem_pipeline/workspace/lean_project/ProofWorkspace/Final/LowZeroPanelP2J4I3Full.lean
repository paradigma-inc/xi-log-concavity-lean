import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J4I3K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J4I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J4I3K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J4I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J4I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J4I3K1Point)
        (theta48PanelCenter 4 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J4I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J4I3Coefficient,lowZeroSeedP2J4I3K1Point,lowZeroSeedP2J4I3K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J4I3K1Point
        (theta48PanelCenter 4 3) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP2J4I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J4I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J4I3K1Point
        (theta48PanelCenter 4 3) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP2J4I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J4I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J4I3K1Point
        (theta48PanelCenter 4 3) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP2J4I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J4I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J4I3K1Point
        (theta48PanelCenter 4 3) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP2J4I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J4I3Coefficient]

def lowZeroPanelP2J4I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP2J4I3Coefficient

theorem lowZeroPanelP2J4I3Value_eq : lowZeroPanelP2J4I3Value=(194821975428349631416252176439792235285438083383368296881982051576610393452517659425698635702491435386377118926459001581939559405106233454193558263597665681:ℚ)/9606675870402253207300954968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J4I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J4I3K1Point (theta48PanelCenter 4 3)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP2J4I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J4I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J4I3K1Point (theta48PanelCenter 4 3)
    ((1:ℚ)/1) lowZeroPanelP2J4I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J4I3Value,theta48PanelHalfWidth]

end ReciprocalXi
