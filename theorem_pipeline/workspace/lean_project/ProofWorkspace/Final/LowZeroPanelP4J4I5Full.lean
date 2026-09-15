import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J4I5K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J4I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J4I5K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J4I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J4I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J4I5K1Point)
        (theta48PanelCenter 4 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J4I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J4I5Coefficient,lowZeroSeedP4J4I5K1Point,lowZeroSeedP4J4I5K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I5K1Point
        (theta48PanelCenter 4 5) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP4J4I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I5Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I5K1Point
        (theta48PanelCenter 4 5) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP4J4I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I5Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I5K1Point
        (theta48PanelCenter 4 5) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP4J4I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I5Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I5K1Point
        (theta48PanelCenter 4 5) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP4J4I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I5Coefficient]

def lowZeroPanelP4J4I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP4J4I5Coefficient

theorem lowZeroPanelP4J4I5Value_eq : lowZeroPanelP4J4I5Value=(-230118937544020149581828454859563890660731279311763680743729183482085395882953915370287421603095314719070965697353594500030539254126550277738478717305578087:ℚ)/1266947627140389957485264543188687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J4I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J4I5K1Point (theta48PanelCenter 4 5)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP4J4I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J4I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J4I5K1Point (theta48PanelCenter 4 5)
    ((1:ℚ)/1) lowZeroPanelP4J4I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J4I5Value,theta48PanelHalfWidth]

end ReciprocalXi
