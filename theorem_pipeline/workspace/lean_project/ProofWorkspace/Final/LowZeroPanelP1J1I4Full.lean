import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I4K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J1I4K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J1I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J1I4K1State n
  | 1 => lowZeroCoefficientsP1J1I4K2State n
  | 2 => lowZeroCoefficientsP1J1I4K3State n
  | 3 => lowZeroCoefficientsP1J1I4K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP1J1I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J1I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J1I4K1Point)
        (theta48PanelCenter 1 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J1I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I4Coefficient,lowZeroSeedP1J1I4K1Point,lowZeroSeedP1J1I4K1Point]
  · convert lowZeroCoefficientsP1J1I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I4Coefficient,lowZeroSeedP1J1I4K1Point,lowZeroSeedP1J1I4K2Point]
  · convert lowZeroCoefficientsP1J1I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I4Coefficient,lowZeroSeedP1J1I4K1Point,lowZeroSeedP1J1I4K3Point]
  · convert lowZeroCoefficientsP1J1I4K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J1I4Coefficient,lowZeroSeedP1J1I4K1Point,lowZeroSeedP1J1I4K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J1I4K1Point
        (theta48PanelCenter 1 4) (theta48PanelHalfWidth 1) 5 n
        (by norm_num [lowZeroSeedP1J1I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J1I4Coefficient]

def lowZeroPanelP1J1I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP1J1I4Coefficient

theorem lowZeroPanelP1J1I4Value_eq : lowZeroPanelP1J1I4Value=(-150966022736775609830807869682152201640516648346342725455389910592756471877879553917173844104969805283906405238886938106207449006109091709740490994234582066541078472150199887994517047853:ℚ)/81738556589702577902275131818625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J1I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J1I4K1Point (theta48PanelCenter 1 4)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP1J1I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J1I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J1I4K1Point (theta48PanelCenter 1 4)
    ((1:ℚ)/8) lowZeroPanelP1J1I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J1I4Value,theta48PanelHalfWidth]

end ReciprocalXi
