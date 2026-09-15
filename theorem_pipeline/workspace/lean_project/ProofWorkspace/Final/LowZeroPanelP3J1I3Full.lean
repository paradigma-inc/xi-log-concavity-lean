import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I3K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I3K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I3K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I3K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J1I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J1I3K1State n
  | 1 => lowZeroCoefficientsP3J1I3K2State n
  | 2 => lowZeroCoefficientsP3J1I3K3State n
  | 3 => lowZeroCoefficientsP3J1I3K4State n
  | 4 => lowZeroCoefficientsP3J1I3K5State n
  | _ => (0,0)

theorem lowZeroPanelP3J1I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J1I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J1I3K1Point)
        (theta48PanelCenter 1 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J1I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I3Coefficient,lowZeroSeedP3J1I3K1Point,lowZeroSeedP3J1I3K1Point]
  · convert lowZeroCoefficientsP3J1I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I3Coefficient,lowZeroSeedP3J1I3K1Point,lowZeroSeedP3J1I3K2Point]
  · convert lowZeroCoefficientsP3J1I3K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I3Coefficient,lowZeroSeedP3J1I3K1Point,lowZeroSeedP3J1I3K3Point]
  · convert lowZeroCoefficientsP3J1I3K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I3Coefficient,lowZeroSeedP3J1I3K1Point,lowZeroSeedP3J1I3K4Point]
  · convert lowZeroCoefficientsP3J1I3K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I3Coefficient,lowZeroSeedP3J1I3K1Point,lowZeroSeedP3J1I3K5Point]

def lowZeroPanelP3J1I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP3J1I3Coefficient

theorem lowZeroPanelP3J1I3Value_eq : lowZeroPanelP3J1I3Value=(268647705077292777564986515120906823673393112891303309622507477629335621789063398032786488223174657899076960355547172219562977009623634720825433521186125817283135819887805631419498335081:ℚ)/273934622084408639456273414743500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J1I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J1I3K1Point (theta48PanelCenter 1 3)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP3J1I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J1I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J1I3K1Point (theta48PanelCenter 1 3)
    ((1:ℚ)/8) lowZeroPanelP3J1I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J1I3Value,theta48PanelHalfWidth]

end ReciprocalXi
