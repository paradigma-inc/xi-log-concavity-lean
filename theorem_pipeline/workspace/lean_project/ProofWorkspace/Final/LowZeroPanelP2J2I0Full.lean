import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J2I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J2I0K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J2I0K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J2I0K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J2I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J2I0K1State n
  | 1 => lowZeroCoefficientsP2J2I0K2State n
  | 2 => lowZeroCoefficientsP2J2I0K3State n
  | 3 => lowZeroCoefficientsP2J2I0K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J2I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J2I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J2I0K1Point)
        (theta48PanelCenter 2 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J2I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J2I0Coefficient,lowZeroSeedP2J2I0K1Point,lowZeroSeedP2J2I0K1Point]
  · convert lowZeroCoefficientsP2J2I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J2I0Coefficient,lowZeroSeedP2J2I0K1Point,lowZeroSeedP2J2I0K2Point]
  · convert lowZeroCoefficientsP2J2I0K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J2I0Coefficient,lowZeroSeedP2J2I0K1Point,lowZeroSeedP2J2I0K3Point]
  · convert lowZeroCoefficientsP2J2I0K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J2I0Coefficient,lowZeroSeedP2J2I0K1Point,lowZeroSeedP2J2I0K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J2I0K1Point
        (theta48PanelCenter 2 0) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP2J2I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J2I0Coefficient]

def lowZeroPanelP2J2I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP2J2I0Coefficient

theorem lowZeroPanelP2J2I0Value_eq : lowZeroPanelP2J2I0Value=(-449991748328862258397805445524740671811009321361225129691362953249515814375197475465853214867529580515056464045056166584779208812648479663506510395257212342554838716962561341704315579361:ℚ)/1013558101712311965988211634550950000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J2I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J2I0K1Point (theta48PanelCenter 2 0)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP2J2I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J2I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J2I0K1Point (theta48PanelCenter 2 0)
    ((1:ℚ)/4) lowZeroPanelP2J2I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J2I0Value,theta48PanelHalfWidth]

end ReciprocalXi
