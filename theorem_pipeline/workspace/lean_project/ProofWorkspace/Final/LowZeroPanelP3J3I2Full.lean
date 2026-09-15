import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J3I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J3I2K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J3I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J3I2K1State n
  | 1 => lowZeroCoefficientsP3J3I2K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J3I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J3I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J3I2K1Point)
        (theta48PanelCenter 3 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J3I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J3I2Coefficient,lowZeroSeedP3J3I2K1Point,lowZeroSeedP3J3I2K1Point]
  · convert lowZeroCoefficientsP3J3I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J3I2Coefficient,lowZeroSeedP3J3I2K1Point,lowZeroSeedP3J3I2K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I2K1Point
        (theta48PanelCenter 3 2) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP3J3I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I2K1Point
        (theta48PanelCenter 3 2) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP3J3I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I2K1Point
        (theta48PanelCenter 3 2) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP3J3I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I2Coefficient]

def lowZeroPanelP3J3I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP3J3I2Coefficient

theorem lowZeroPanelP3J3I2Value_eq : lowZeroPanelP3J3I2Value=(3779787115283510445447081493367653919692380134469054099595987422699784501969296608650887406638360312692869602110818959968064230974552800280174351305679080888817898201615524711:ℚ)/2031992986592445801900985634625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J3I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J3I2K1Point (theta48PanelCenter 3 2)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP3J3I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J3I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J3I2K1Point (theta48PanelCenter 3 2)
    ((1:ℚ)/2) lowZeroPanelP3J3I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J3I2Value,theta48PanelHalfWidth]

end ReciprocalXi
