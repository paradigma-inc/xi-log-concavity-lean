import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J2I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J2I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J2I1K3Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J2I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J2I1K1State n
  | 1 => lowZeroCoefficientsP1J2I1K2State n
  | 2 => lowZeroCoefficientsP1J2I1K3State n
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP1J2I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J2I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J2I1K1Point)
        (theta48PanelCenter 2 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J2I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J2I1Coefficient,lowZeroSeedP1J2I1K1Point,lowZeroSeedP1J2I1K1Point]
  · convert lowZeroCoefficientsP1J2I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J2I1Coefficient,lowZeroSeedP1J2I1K1Point,lowZeroSeedP1J2I1K2Point]
  · convert lowZeroCoefficientsP1J2I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J2I1Coefficient,lowZeroSeedP1J2I1K1Point,lowZeroSeedP1J2I1K3Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J2I1K1Point
        (theta48PanelCenter 2 1) (theta48PanelHalfWidth 2) 4 n
        (by norm_num [lowZeroSeedP1J2I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J2I1Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J2I1K1Point
        (theta48PanelCenter 2 1) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP1J2I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J2I1Coefficient]

def lowZeroPanelP1J2I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP1J2I1Coefficient

theorem lowZeroPanelP1J2I1Value_eq : lowZeroPanelP1J2I1Value=(-25037105791868449807284015408381326706667612118456948193301306839707082694116922825833760282503199552851244721552847759293640380662233358423039439964936653716900046122261639357329349:ℚ)/2594874812371510409596035930750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J2I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J2I1K1Point (theta48PanelCenter 2 1)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP1J2I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J2I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J2I1K1Point (theta48PanelCenter 2 1)
    ((1:ℚ)/4) lowZeroPanelP1J2I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J2I1Value,theta48PanelHalfWidth]

end ReciprocalXi
