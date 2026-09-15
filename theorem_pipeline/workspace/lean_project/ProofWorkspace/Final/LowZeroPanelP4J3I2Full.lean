import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J3I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J3I2K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J3I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J3I2K1State n
  | 1 => lowZeroCoefficientsP4J3I2K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J3I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J3I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J3I2K1Point)
        (theta48PanelCenter 3 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J3I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J3I2Coefficient,lowZeroSeedP4J3I2K1Point,lowZeroSeedP4J3I2K1Point]
  · convert lowZeroCoefficientsP4J3I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J3I2Coefficient,lowZeroSeedP4J3I2K1Point,lowZeroSeedP4J3I2K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I2K1Point
        (theta48PanelCenter 3 2) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP4J3I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I2K1Point
        (theta48PanelCenter 3 2) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP4J3I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I2K1Point
        (theta48PanelCenter 3 2) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP4J3I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I2Coefficient]

def lowZeroPanelP4J3I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP4J3I2Coefficient

theorem lowZeroPanelP4J3I2Value_eq : lowZeroPanelP4J3I2Value=(-4708166988481969710168021486744445701082664309584738021982968481921423144815835928164746084747489686710095695833255082144291275254513874946104776685610743920333234206677135809:ℚ)/3060259968938139993925759766156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J3I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J3I2K1Point (theta48PanelCenter 3 2)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP4J3I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J3I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J3I2K1Point (theta48PanelCenter 3 2)
    ((1:ℚ)/2) lowZeroPanelP4J3I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J3I2Value,theta48PanelHalfWidth]

end ReciprocalXi
