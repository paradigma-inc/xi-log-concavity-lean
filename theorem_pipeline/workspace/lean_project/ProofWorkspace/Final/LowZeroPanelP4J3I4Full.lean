import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J3I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J3I4K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J3I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J3I4K1State n
  | 1 => lowZeroCoefficientsP4J3I4K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J3I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J3I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J3I4K1Point)
        (theta48PanelCenter 3 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J3I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J3I4Coefficient,lowZeroSeedP4J3I4K1Point,lowZeroSeedP4J3I4K1Point]
  · convert lowZeroCoefficientsP4J3I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J3I4Coefficient,lowZeroSeedP4J3I4K1Point,lowZeroSeedP4J3I4K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I4K1Point
        (theta48PanelCenter 3 4) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP4J3I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I4K1Point
        (theta48PanelCenter 3 4) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP4J3I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I4K1Point
        (theta48PanelCenter 3 4) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP4J3I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I4Coefficient]

def lowZeroPanelP4J3I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP4J3I4Coefficient

theorem lowZeroPanelP4J3I4Value_eq : lowZeroPanelP4J3I4Value=(881428142657346178015023792441257413220286823323351715355823685370325612289445923865488957245733055164014536040308116424112738141944180019012785069295501184444802437765232551:ℚ)/230354114025525446815502644216125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J3I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J3I4K1Point (theta48PanelCenter 3 4)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP4J3I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J3I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J3I4K1Point (theta48PanelCenter 3 4)
    ((1:ℚ)/2) lowZeroPanelP4J3I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J3I4Value,theta48PanelHalfWidth]

end ReciprocalXi
