import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I1K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I1K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I1K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I1K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J1I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J1I1K1State n
  | 1 => lowZeroCoefficientsP2J1I1K2State n
  | 2 => lowZeroCoefficientsP2J1I1K3State n
  | 3 => lowZeroCoefficientsP2J1I1K4State n
  | 4 => lowZeroCoefficientsP2J1I1K5State n
  | _ => (0,0)

theorem lowZeroPanelP2J1I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J1I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J1I1K1Point)
        (theta48PanelCenter 1 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J1I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I1Coefficient,lowZeroSeedP2J1I1K1Point,lowZeroSeedP2J1I1K1Point]
  · convert lowZeroCoefficientsP2J1I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I1Coefficient,lowZeroSeedP2J1I1K1Point,lowZeroSeedP2J1I1K2Point]
  · convert lowZeroCoefficientsP2J1I1K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I1Coefficient,lowZeroSeedP2J1I1K1Point,lowZeroSeedP2J1I1K3Point]
  · convert lowZeroCoefficientsP2J1I1K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I1Coefficient,lowZeroSeedP2J1I1K1Point,lowZeroSeedP2J1I1K4Point]
  · convert lowZeroCoefficientsP2J1I1K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I1Coefficient,lowZeroSeedP2J1I1K1Point,lowZeroSeedP2J1I1K5Point]

def lowZeroPanelP2J1I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP2J1I1Coefficient

theorem lowZeroPanelP2J1I1Value_eq : lowZeroPanelP2J1I1Value=(-62093673718461976933559947222626655332807380147309951593909115463886948100279399403472193561149019037900733577553187967787526202565666497722372447405008719206244738429238714012513543136009:ℚ)/460708228051050893631005288432250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J1I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J1I1K1Point (theta48PanelCenter 1 1)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP2J1I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J1I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J1I1K1Point (theta48PanelCenter 1 1)
    ((1:ℚ)/8) lowZeroPanelP2J1I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J1I1Value,theta48PanelHalfWidth]

end ReciprocalXi
