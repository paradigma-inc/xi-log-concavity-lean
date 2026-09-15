import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I2K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I2K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I2K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I2K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I2K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J1I2Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J1I2K1State n
  | 1 => lowZeroCoefficientsP4J1I2K2State n
  | 2 => lowZeroCoefficientsP4J1I2K3State n
  | 3 => lowZeroCoefficientsP4J1I2K4State n
  | 4 => lowZeroCoefficientsP4J1I2K5State n
  | _ => (0,0)

theorem lowZeroPanelP4J1I2_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J1I2Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J1I2K1Point)
        (theta48PanelCenter 1 2:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J1I2K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I2Coefficient,lowZeroSeedP4J1I2K1Point,lowZeroSeedP4J1I2K1Point]
  · convert lowZeroCoefficientsP4J1I2K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I2Coefficient,lowZeroSeedP4J1I2K1Point,lowZeroSeedP4J1I2K2Point]
  · convert lowZeroCoefficientsP4J1I2K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I2Coefficient,lowZeroSeedP4J1I2K1Point,lowZeroSeedP4J1I2K3Point]
  · convert lowZeroCoefficientsP4J1I2K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I2Coefficient,lowZeroSeedP4J1I2K1Point,lowZeroSeedP4J1I2K4Point]
  · convert lowZeroCoefficientsP4J1I2K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I2Coefficient,lowZeroSeedP4J1I2K1Point,lowZeroSeedP4J1I2K5Point]

def lowZeroPanelP4J1I2Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP4J1I2Coefficient

theorem lowZeroPanelP4J1I2Value_eq : lowZeroPanelP4J1I2Value=(20857047637282262497150406894391553523450866910512481445580409013253625410014296748647291730721013393353490383779800904045614908623077809657980382336481103819777938001298641376292156480417:ℚ)/405423240684924786395284653820380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J1I2_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J1I2K1Point (theta48PanelCenter 1 2)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP4J1I2Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J1I2_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J1I2K1Point (theta48PanelCenter 1 2)
    ((1:ℚ)/8) lowZeroPanelP4J1I2Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J1I2Value,theta48PanelHalfWidth]

end ReciprocalXi
