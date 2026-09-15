import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J2I5K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J2I5K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J2I5K3Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J2I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J2I5K1State n
  | 1 => lowZeroCoefficientsP2J2I5K2State n
  | 2 => lowZeroCoefficientsP2J2I5K3State n
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J2I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J2I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J2I5K1Point)
        (theta48PanelCenter 2 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J2I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J2I5Coefficient,lowZeroSeedP2J2I5K1Point,lowZeroSeedP2J2I5K1Point]
  · convert lowZeroCoefficientsP2J2I5K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J2I5Coefficient,lowZeroSeedP2J2I5K1Point,lowZeroSeedP2J2I5K2Point]
  · convert lowZeroCoefficientsP2J2I5K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J2I5Coefficient,lowZeroSeedP2J2I5K1Point,lowZeroSeedP2J2I5K3Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J2I5K1Point
        (theta48PanelCenter 2 5) (theta48PanelHalfWidth 2) 4 n
        (by norm_num [lowZeroSeedP2J2I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J2I5Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J2I5K1Point
        (theta48PanelCenter 2 5) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP2J2I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J2I5Coefficient]

def lowZeroPanelP2J2I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP2J2I5Coefficient

theorem lowZeroPanelP2J2I5Value_eq : lowZeroPanelP2J2I5Value=(89168405134368559187660886601640201356101645110543458954037587796985519605596275233750338591676742881140541577400629278973238178266414544678168467027014786141164527072688905698384229:ℚ)/1266947627140389957485264543188687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J2I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J2I5K1Point (theta48PanelCenter 2 5)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP2J2I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J2I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J2I5K1Point (theta48PanelCenter 2 5)
    ((1:ℚ)/4) lowZeroPanelP2J2I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J2I5Value,theta48PanelHalfWidth]

end ReciprocalXi
