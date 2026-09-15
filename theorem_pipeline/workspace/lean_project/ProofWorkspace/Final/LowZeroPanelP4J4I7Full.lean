import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J4I7K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J4I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J4I7K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J4I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J4I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J4I7K1Point)
        (theta48PanelCenter 4 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J4I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J4I7Coefficient,lowZeroSeedP4J4I7K1Point,lowZeroSeedP4J4I7K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I7K1Point
        (theta48PanelCenter 4 7) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP4J4I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I7K1Point
        (theta48PanelCenter 4 7) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP4J4I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I7K1Point
        (theta48PanelCenter 4 7) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP4J4I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I7K1Point
        (theta48PanelCenter 4 7) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP4J4I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I7Coefficient]

def lowZeroPanelP4J4I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP4J4I7Coefficient

theorem lowZeroPanelP4J4I7Value_eq : lowZeroPanelP4J4I7Value=(121713120153996429196709040163396999094328289970218064164911800449867692825562766793371331397769991664285263416349141955218578893786789197215725583:ℚ)/859530276214647189610084493343750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J4I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J4I7K1Point (theta48PanelCenter 4 7)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP4J4I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J4I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J4I7K1Point (theta48PanelCenter 4 7)
    ((1:ℚ)/1) lowZeroPanelP4J4I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J4I7Value,theta48PanelHalfWidth]

end ReciprocalXi
