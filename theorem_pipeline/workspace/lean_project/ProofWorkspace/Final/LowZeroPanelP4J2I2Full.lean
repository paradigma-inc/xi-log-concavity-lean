import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J2I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J2I2K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J2I2K3Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J2I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J2I2K1State n
  | 1 => lowZeroCoefficientsP4J2I2K2State n
  | 2 => lowZeroCoefficientsP4J2I2K3State n
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J2I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J2I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J2I2K1Point)
        (theta48PanelCenter 2 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J2I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J2I2Coefficient,lowZeroSeedP4J2I2K1Point,lowZeroSeedP4J2I2K1Point]
  · convert lowZeroCoefficientsP4J2I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J2I2Coefficient,lowZeroSeedP4J2I2K1Point,lowZeroSeedP4J2I2K2Point]
  · convert lowZeroCoefficientsP4J2I2K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J2I2Coefficient,lowZeroSeedP4J2I2K1Point,lowZeroSeedP4J2I2K3Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J2I2K1Point
        (theta48PanelCenter 2 2) (theta48PanelHalfWidth 2) 4 n
        (by norm_num [lowZeroSeedP4J2I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J2I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J2I2K1Point
        (theta48PanelCenter 2 2) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP4J2I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J2I2Coefficient]

def lowZeroPanelP4J2I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP4J2I2Coefficient

theorem lowZeroPanelP4J2I2Value_eq : lowZeroPanelP4J2I2Value=(-2013593715760069736054211575571808529713136460519901762653171607745883933939370510028123679643422395630117512546649478411871648213442316932815263133296910121543871478062428182927247597:ℚ)/633473813570194978742632271594343750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J2I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J2I2K1Point (theta48PanelCenter 2 2)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP4J2I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J2I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J2I2K1Point (theta48PanelCenter 2 2)
    ((1:ℚ)/4) lowZeroPanelP4J2I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J2I2Value,theta48PanelHalfWidth]

end ReciprocalXi
