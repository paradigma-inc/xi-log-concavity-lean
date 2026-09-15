import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I4K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I4K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I4K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J0I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J0I4K1State n
  | 1 => lowZeroCoefficientsP4J0I4K2State n
  | 2 => lowZeroCoefficientsP4J0I4K3State n
  | 3 => lowZeroCoefficientsP4J0I4K4State n
  | 4 => lowZeroCoefficientsP4J0I4K5State n
  | _ => (0,0)

theorem lowZeroPanelP4J0I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J0I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J0I4K1Point)
        (theta48PanelCenter 0 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J0I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I4Coefficient,lowZeroSeedP4J0I4K1Point,lowZeroSeedP4J0I4K1Point]
  · convert lowZeroCoefficientsP4J0I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I4Coefficient,lowZeroSeedP4J0I4K1Point,lowZeroSeedP4J0I4K2Point]
  · convert lowZeroCoefficientsP4J0I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I4Coefficient,lowZeroSeedP4J0I4K1Point,lowZeroSeedP4J0I4K3Point]
  · convert lowZeroCoefficientsP4J0I4K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I4Coefficient,lowZeroSeedP4J0I4K1Point,lowZeroSeedP4J0I4K4Point]
  · convert lowZeroCoefficientsP4J0I4K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I4Coefficient,lowZeroSeedP4J0I4K1Point,lowZeroSeedP4J0I4K5Point]

def lowZeroPanelP4J0I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP4J0I4Coefficient

theorem lowZeroPanelP4J0I4Value_eq : lowZeroPanelP4J0I4Value=(142242378389743268387971635750889622716158339496874391261856689622402554330661530563860501633278146000119682179620235686936169817717611880193069662995740459519003248543497161719605573981817:ℚ)/151277328613777905371374870828500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J0I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J0I4K1Point (theta48PanelCenter 0 4)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP4J0I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J0I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J0I4K1Point (theta48PanelCenter 0 4)
    ((1:ℚ)/16) lowZeroPanelP4J0I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J0I4Value,theta48PanelHalfWidth]

end ReciprocalXi
