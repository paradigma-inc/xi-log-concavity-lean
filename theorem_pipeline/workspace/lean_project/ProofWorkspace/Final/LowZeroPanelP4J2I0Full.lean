import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J2I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J2I0K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J2I0K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J2I0K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J2I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J2I0K1State n
  | 1 => lowZeroCoefficientsP4J2I0K2State n
  | 2 => lowZeroCoefficientsP4J2I0K3State n
  | 3 => lowZeroCoefficientsP4J2I0K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J2I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J2I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J2I0K1Point)
        (theta48PanelCenter 2 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J2I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J2I0Coefficient,lowZeroSeedP4J2I0K1Point,lowZeroSeedP4J2I0K1Point]
  · convert lowZeroCoefficientsP4J2I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J2I0Coefficient,lowZeroSeedP4J2I0K1Point,lowZeroSeedP4J2I0K2Point]
  · convert lowZeroCoefficientsP4J2I0K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J2I0Coefficient,lowZeroSeedP4J2I0K1Point,lowZeroSeedP4J2I0K3Point]
  · convert lowZeroCoefficientsP4J2I0K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J2I0Coefficient,lowZeroSeedP4J2I0K1Point,lowZeroSeedP4J2I0K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J2I0K1Point
        (theta48PanelCenter 2 0) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP4J2I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J2I0Coefficient]

def lowZeroPanelP4J2I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP4J2I0Coefficient

theorem lowZeroPanelP4J2I0Value_eq : lowZeroPanelP4J2I0Value=(160268184110586581289329683736558020815449485124831929932076241681104757850798937986009743347884747593009450862483078135824243339048184708843876214427233891388603727260889715021411388471:ℚ)/506779050856155982994105817275475000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J2I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J2I0K1Point (theta48PanelCenter 2 0)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP4J2I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J2I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J2I0K1Point (theta48PanelCenter 2 0)
    ((1:ℚ)/4) lowZeroPanelP4J2I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J2I0Value,theta48PanelHalfWidth]

end ReciprocalXi
