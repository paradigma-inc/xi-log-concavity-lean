import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I0K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I0K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I0K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J0I0K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J0I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J0I0K1State n
  | 1 => lowZeroCoefficientsP3J0I0K2State n
  | 2 => lowZeroCoefficientsP3J0I0K3State n
  | 3 => lowZeroCoefficientsP3J0I0K4State n
  | 4 => lowZeroCoefficientsP3J0I0K5State n
  | _ => (0,0)

theorem lowZeroPanelP3J0I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J0I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J0I0K1Point)
        (theta48PanelCenter 0 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J0I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I0Coefficient,lowZeroSeedP3J0I0K1Point,lowZeroSeedP3J0I0K1Point]
  · convert lowZeroCoefficientsP3J0I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I0Coefficient,lowZeroSeedP3J0I0K1Point,lowZeroSeedP3J0I0K2Point]
  · convert lowZeroCoefficientsP3J0I0K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I0Coefficient,lowZeroSeedP3J0I0K1Point,lowZeroSeedP3J0I0K3Point]
  · convert lowZeroCoefficientsP3J0I0K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I0Coefficient,lowZeroSeedP3J0I0K1Point,lowZeroSeedP3J0I0K4Point]
  · convert lowZeroCoefficientsP3J0I0K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J0I0Coefficient,lowZeroSeedP3J0I0K1Point,lowZeroSeedP3J0I0K5Point]

def lowZeroPanelP3J0I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP3J0I0Coefficient

theorem lowZeroPanelP3J0I0Value_eq : lowZeroPanelP3J0I0Value=(27241319084065113476505971187613179469330165925234145145814284483448262681401080340010419267788625449039140530863789145170530286232583018187770925530887690002572747016723524272664579354682771:ℚ)/4054232406849247863952846538203800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J0I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J0I0K1Point (theta48PanelCenter 0 0)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP3J0I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J0I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J0I0K1Point (theta48PanelCenter 0 0)
    ((1:ℚ)/16) lowZeroPanelP3J0I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J0I0Value,theta48PanelHalfWidth]

end ReciprocalXi
