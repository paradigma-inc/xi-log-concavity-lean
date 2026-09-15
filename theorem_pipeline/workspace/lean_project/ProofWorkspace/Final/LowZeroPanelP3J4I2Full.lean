import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J4I2K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J4I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J4I2K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J4I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J4I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J4I2K1Point)
        (theta48PanelCenter 4 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J4I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J4I2Coefficient,lowZeroSeedP3J4I2K1Point,lowZeroSeedP3J4I2K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I2K1Point
        (theta48PanelCenter 4 2) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP3J4I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I2K1Point
        (theta48PanelCenter 4 2) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP3J4I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I2K1Point
        (theta48PanelCenter 4 2) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP3J4I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I2K1Point
        (theta48PanelCenter 4 2) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP3J4I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I2Coefficient]

def lowZeroPanelP3J4I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP3J4I2Coefficient

theorem lowZeroPanelP3J4I2Value_eq : lowZeroPanelP3J4I2Value=(302419435975942952689424803113505629417138712811383965870546577320457670194623627010650589833635200157101254973673105230874008316316025205597304175635148814730527:ℚ)/9180779906814419981777279298468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J4I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J4I2K1Point (theta48PanelCenter 4 2)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP3J4I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J4I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J4I2K1Point (theta48PanelCenter 4 2)
    ((1:ℚ)/1) lowZeroPanelP3J4I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J4I2Value,theta48PanelHalfWidth]

end ReciprocalXi
