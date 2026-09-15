import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I0K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I0K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I0K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I0K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J1I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J1I0K1State n
  | 1 => lowZeroCoefficientsP2J1I0K2State n
  | 2 => lowZeroCoefficientsP2J1I0K3State n
  | 3 => lowZeroCoefficientsP2J1I0K4State n
  | 4 => lowZeroCoefficientsP2J1I0K5State n
  | _ => (0,0)

theorem lowZeroPanelP2J1I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J1I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J1I0K1Point)
        (theta48PanelCenter 1 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J1I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I0Coefficient,lowZeroSeedP2J1I0K1Point,lowZeroSeedP2J1I0K1Point]
  · convert lowZeroCoefficientsP2J1I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I0Coefficient,lowZeroSeedP2J1I0K1Point,lowZeroSeedP2J1I0K2Point]
  · convert lowZeroCoefficientsP2J1I0K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I0Coefficient,lowZeroSeedP2J1I0K1Point,lowZeroSeedP2J1I0K3Point]
  · convert lowZeroCoefficientsP2J1I0K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I0Coefficient,lowZeroSeedP2J1I0K1Point,lowZeroSeedP2J1I0K4Point]
  · convert lowZeroCoefficientsP2J1I0K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I0Coefficient,lowZeroSeedP2J1I0K1Point,lowZeroSeedP2J1I0K5Point]

def lowZeroPanelP2J1I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP2J1I0Coefficient

theorem lowZeroPanelP2J1I0Value_eq : lowZeroPanelP2J1I0Value=(9946380819628691785235795301034182148796052391745927255937087991874844094025242955394638852378627762095470378603352082169107047125063904474215233906146893959032095214840936357513440297121:ℚ)/1013558101712311965988211634550950000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J1I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J1I0K1Point (theta48PanelCenter 1 0)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP2J1I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J1I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J1I0K1Point (theta48PanelCenter 1 0)
    ((1:ℚ)/8) lowZeroPanelP2J1I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J1I0Value,theta48PanelHalfWidth]

end ReciprocalXi
