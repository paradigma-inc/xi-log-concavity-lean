import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J3I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J3I3K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J3I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J3I3K1State n
  | 1 => lowZeroCoefficientsP1J3I3K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP1J3I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J3I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J3I3K1Point)
        (theta48PanelCenter 3 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J3I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J3I3Coefficient,lowZeroSeedP1J3I3K1Point,lowZeroSeedP1J3I3K1Point]
  · convert lowZeroCoefficientsP1J3I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J3I3Coefficient,lowZeroSeedP1J3I3K1Point,lowZeroSeedP1J3I3K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP1J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP1J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP1J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I3Coefficient]

def lowZeroPanelP1J3I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP1J3I3Coefficient

theorem lowZeroPanelP1J3I3Value_eq : lowZeroPanelP1J3I3Value=(-4389870434562090887682104294728171815320285699179339489136253009629549472414681763661502860572757907175692953389380697442648183243131547500732600636405290208216571547556780177:ℚ)/281543917142308879441169898486375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J3I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J3I3K1Point (theta48PanelCenter 3 3)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP1J3I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J3I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J3I3K1Point (theta48PanelCenter 3 3)
    ((1:ℚ)/2) lowZeroPanelP1J3I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J3I3Value,theta48PanelHalfWidth]

end ReciprocalXi
