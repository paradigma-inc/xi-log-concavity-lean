import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I5K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I5K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I5K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I5K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J0I5K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J0I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J0I5K1State n
  | 1 => lowZeroCoefficientsP4J0I5K2State n
  | 2 => lowZeroCoefficientsP4J0I5K3State n
  | 3 => lowZeroCoefficientsP4J0I5K4State n
  | 4 => lowZeroCoefficientsP4J0I5K5State n
  | _ => (0,0)

theorem lowZeroPanelP4J0I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J0I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J0I5K1Point)
        (theta48PanelCenter 0 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J0I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I5Coefficient,lowZeroSeedP4J0I5K1Point,lowZeroSeedP4J0I5K1Point]
  · convert lowZeroCoefficientsP4J0I5K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I5Coefficient,lowZeroSeedP4J0I5K1Point,lowZeroSeedP4J0I5K2Point]
  · convert lowZeroCoefficientsP4J0I5K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I5Coefficient,lowZeroSeedP4J0I5K1Point,lowZeroSeedP4J0I5K3Point]
  · convert lowZeroCoefficientsP4J0I5K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I5Coefficient,lowZeroSeedP4J0I5K1Point,lowZeroSeedP4J0I5K4Point]
  · convert lowZeroCoefficientsP4J0I5K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J0I5Coefficient,lowZeroSeedP4J0I5K1Point,lowZeroSeedP4J0I5K5Point]

def lowZeroPanelP4J0I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP4J0I5Coefficient

theorem lowZeroPanelP4J0I5Value_eq : lowZeroPanelP4J0I5Value=(2180951489528426721109964905502104225662577493550221378581804161761814641369980470016285683137358120454113320155601806342592977874013679508166719832445261161591097486731032404783408709769:ℚ)/2730122832895116406702253561080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J0I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J0I5K1Point (theta48PanelCenter 0 5)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP4J0I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J0I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J0I5K1Point (theta48PanelCenter 0 5)
    ((1:ℚ)/16) lowZeroPanelP4J0I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J0I5Value,theta48PanelHalfWidth]

end ReciprocalXi
