import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J3I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J3I0K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J3I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J3I0K1State n
  | 1 => lowZeroCoefficientsP5J3I0K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP5J3I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J3I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J3I0K1Point)
        (theta48PanelCenter 3 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J3I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J3I0Coefficient,lowZeroSeedP5J3I0K1Point,lowZeroSeedP5J3I0K1Point]
  · convert lowZeroCoefficientsP5J3I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J3I0Coefficient,lowZeroSeedP5J3I0K1Point,lowZeroSeedP5J3I0K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J3I0K1Point
        (theta48PanelCenter 3 0) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP5J3I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J3I0Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J3I0K1Point
        (theta48PanelCenter 3 0) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP5J3I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J3I0Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J3I0K1Point
        (theta48PanelCenter 3 0) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP5J3I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J3I0Coefficient]

def lowZeroPanelP5J3I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP5J3I0Coefficient

theorem lowZeroPanelP5J3I0Value_eq : lowZeroPanelP5J3I0Value=(1184163258566944755708793814716584463712616271971127719544674720080865473058086068710248739352930299825439759266279450364772305811747718401833523092056847131666118500043387361153:ℚ)/2812314377670121992198145489875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J3I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J3I0K1Point (theta48PanelCenter 3 0)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP5J3I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J3I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J3I0K1Point (theta48PanelCenter 3 0)
    ((1:ℚ)/2) lowZeroPanelP5J3I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J3I0Value,theta48PanelHalfWidth]

end ReciprocalXi
