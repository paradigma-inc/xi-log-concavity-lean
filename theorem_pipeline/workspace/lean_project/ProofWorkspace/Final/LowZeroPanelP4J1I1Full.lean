import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I1K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I1K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I1K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J1I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J1I1K1State n
  | 1 => lowZeroCoefficientsP4J1I1K2State n
  | 2 => lowZeroCoefficientsP4J1I1K3State n
  | 3 => lowZeroCoefficientsP4J1I1K4State n
  | 4 => lowZeroCoefficientsP4J1I1K5State n
  | _ => (0,0)

theorem lowZeroPanelP4J1I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J1I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J1I1K1Point)
        (theta48PanelCenter 1 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J1I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I1Coefficient,lowZeroSeedP4J1I1K1Point,lowZeroSeedP4J1I1K1Point]
  · convert lowZeroCoefficientsP4J1I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I1Coefficient,lowZeroSeedP4J1I1K1Point,lowZeroSeedP4J1I1K2Point]
  · convert lowZeroCoefficientsP4J1I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I1Coefficient,lowZeroSeedP4J1I1K1Point,lowZeroSeedP4J1I1K3Point]
  · convert lowZeroCoefficientsP4J1I1K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I1Coefficient,lowZeroSeedP4J1I1K1Point,lowZeroSeedP4J1I1K4Point]
  · convert lowZeroCoefficientsP4J1I1K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I1Coefficient,lowZeroSeedP4J1I1K1Point,lowZeroSeedP4J1I1K5Point]

def lowZeroPanelP4J1I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP4J1I1Coefficient

theorem lowZeroPanelP4J1I1Value_eq : lowZeroPanelP4J1I1Value=(-17561136880414475491714147107548189863426084303370551974087247878184938252887512219513821444991940534497003420351880925099260251419350269906554756460605046425798103319923210045945500809:ℚ)/439378403724775431761839619625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J1I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J1I1K1Point (theta48PanelCenter 1 1)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP4J1I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J1I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J1I1K1Point (theta48PanelCenter 1 1)
    ((1:ℚ)/8) lowZeroPanelP4J1I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J1I1Value,theta48PanelHalfWidth]

end ReciprocalXi
