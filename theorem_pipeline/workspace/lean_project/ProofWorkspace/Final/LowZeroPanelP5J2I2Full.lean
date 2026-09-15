import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I2K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I2K3Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J2I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J2I2K1State n
  | 1 => lowZeroCoefficientsP5J2I2K2State n
  | 2 => lowZeroCoefficientsP5J2I2K3State n
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP5J2I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J2I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J2I2K1Point)
        (theta48PanelCenter 2 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J2I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I2Coefficient,lowZeroSeedP5J2I2K1Point,lowZeroSeedP5J2I2K1Point]
  · convert lowZeroCoefficientsP5J2I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I2Coefficient,lowZeroSeedP5J2I2K1Point,lowZeroSeedP5J2I2K2Point]
  · convert lowZeroCoefficientsP5J2I2K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I2Coefficient,lowZeroSeedP5J2I2K1Point,lowZeroSeedP5J2I2K3Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J2I2K1Point
        (theta48PanelCenter 2 2) (theta48PanelHalfWidth 2) 4 n
        (by norm_num [lowZeroSeedP5J2I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J2I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J2I2K1Point
        (theta48PanelCenter 2 2) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP5J2I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J2I2Coefficient]

def lowZeroPanelP5J2I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP5J2I2Coefficient

theorem lowZeroPanelP5J2I2Value_eq : lowZeroPanelP5J2I2Value=(-3221749945216111577686738521260301692458451963211000172056763755270700105673823478205590506786227502449583827094522916391556854825249674046325129141182915832367474603553764450093137829:ℚ)/1013558101712311965988211634550950000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J2I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J2I2K1Point (theta48PanelCenter 2 2)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP5J2I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J2I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J2I2K1Point (theta48PanelCenter 2 2)
    ((1:ℚ)/4) lowZeroPanelP5J2I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J2I2Value,theta48PanelHalfWidth]

end ReciprocalXi
