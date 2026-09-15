import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I3K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I3K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I3K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I3K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J1I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J1I3K1State n
  | 1 => lowZeroCoefficientsP4J1I3K2State n
  | 2 => lowZeroCoefficientsP4J1I3K3State n
  | 3 => lowZeroCoefficientsP4J1I3K4State n
  | 4 => lowZeroCoefficientsP4J1I3K5State n
  | _ => (0,0)

theorem lowZeroPanelP4J1I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J1I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J1I3K1Point)
        (theta48PanelCenter 1 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J1I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I3Coefficient,lowZeroSeedP4J1I3K1Point,lowZeroSeedP4J1I3K1Point]
  · convert lowZeroCoefficientsP4J1I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I3Coefficient,lowZeroSeedP4J1I3K1Point,lowZeroSeedP4J1I3K2Point]
  · convert lowZeroCoefficientsP4J1I3K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I3Coefficient,lowZeroSeedP4J1I3K1Point,lowZeroSeedP4J1I3K3Point]
  · convert lowZeroCoefficientsP4J1I3K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I3Coefficient,lowZeroSeedP4J1I3K1Point,lowZeroSeedP4J1I3K4Point]
  · convert lowZeroCoefficientsP4J1I3K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I3Coefficient,lowZeroSeedP4J1I3K1Point,lowZeroSeedP4J1I3K5Point]

def lowZeroPanelP4J1I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP4J1I3Coefficient

theorem lowZeroPanelP4J1I3Value_eq : lowZeroPanelP4J1I3Value=(228487459227840601703841993668119037801180840989456777433462441631018798237295297948960893154484501376763614570730526343367919100183268147322448723447442733205671280379781206875877201524727:ℚ)/10135581017123119659882116345509500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J1I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J1I3K1Point (theta48PanelCenter 1 3)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP4J1I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J1I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J1I3K1Point (theta48PanelCenter 1 3)
    ((1:ℚ)/8) lowZeroPanelP4J1I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J1I3Value,theta48PanelHalfWidth]

end ReciprocalXi
