import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J4I2K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J4I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J4I2K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J4I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J4I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J4I2K1Point)
        (theta48PanelCenter 4 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J4I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J4I2Coefficient,lowZeroSeedP4J4I2K1Point,lowZeroSeedP4J4I2K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I2K1Point
        (theta48PanelCenter 4 2) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP4J4I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I2K1Point
        (theta48PanelCenter 4 2) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP4J4I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I2K1Point
        (theta48PanelCenter 4 2) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP4J4I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I2Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I2K1Point
        (theta48PanelCenter 4 2) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP4J4I2K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I2Coefficient]

def lowZeroPanelP4J4I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP4J4I2Coefficient

theorem lowZeroPanelP4J4I2Value_eq : lowZeroPanelP4J4I2Value=(156156026870517867828680757434337758057128402816861897001452136142514896252475078382562595226565734129522184759766861005745667826710584861944893799697675585598201:ℚ)/4640833799049047463315987337687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J4I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J4I2K1Point (theta48PanelCenter 4 2)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP4J4I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J4I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J4I2K1Point (theta48PanelCenter 4 2)
    ((1:ℚ)/1) lowZeroPanelP4J4I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J4I2Value,theta48PanelHalfWidth]

end ReciprocalXi
