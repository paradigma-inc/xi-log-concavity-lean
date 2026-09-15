import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I7K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I7K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I7K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I7K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J0I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J0I7K1State n
  | 1 => lowZeroCoefficientsP4J0I7K2State n
  | 2 => lowZeroCoefficientsP4J0I7K3State n
  | 3 => lowZeroCoefficientsP4J0I7K4State n
  | 4 => lowZeroCoefficientsP4J0I7K5State n
  | _ => (0,0)

theorem lowZeroPanelP4J0I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J0I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J0I7K1Point)
        (theta48PanelCenter 0 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J0I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I7Coefficient,lowZeroSeedP4J0I7K1Point,lowZeroSeedP4J0I7K1Point]
  · convert lowZeroCoefficientsP4J0I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I7Coefficient,lowZeroSeedP4J0I7K1Point,lowZeroSeedP4J0I7K2Point]
  · convert lowZeroCoefficientsP4J0I7K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I7Coefficient,lowZeroSeedP4J0I7K1Point,lowZeroSeedP4J0I7K3Point]
  · convert lowZeroCoefficientsP4J0I7K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I7Coefficient,lowZeroSeedP4J0I7K1Point,lowZeroSeedP4J0I7K4Point]
  · convert lowZeroCoefficientsP4J0I7K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I7Coefficient,lowZeroSeedP4J0I7K1Point,lowZeroSeedP4J0I7K5Point]

def lowZeroPanelP4J0I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP4J0I7Coefficient

theorem lowZeroPanelP4J0I7Value_eq : lowZeroPanelP4J0I7Value=(-1292519629982046753807719220617877873071738038815681308544500352131783212350843590902276492627299860815765729654659735091475573094987560859011060363939583336700831597721849639811917223275527:ℚ)/10135581017123119659882116345509500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J0I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J0I7K1Point (theta48PanelCenter 0 7)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP4J0I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J0I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J0I7K1Point (theta48PanelCenter 0 7)
    ((1:ℚ)/16) lowZeroPanelP4J0I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J0I7Value,theta48PanelHalfWidth]

end ReciprocalXi
