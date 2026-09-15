import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I3K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I3K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I3K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I3K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J1I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J1I3K1State n
  | 1 => lowZeroCoefficientsP2J1I3K2State n
  | 2 => lowZeroCoefficientsP2J1I3K3State n
  | 3 => lowZeroCoefficientsP2J1I3K4State n
  | 4 => lowZeroCoefficientsP2J1I3K5State n
  | _ => (0,0)

theorem lowZeroPanelP2J1I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J1I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J1I3K1Point)
        (theta48PanelCenter 1 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J1I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I3Coefficient,lowZeroSeedP2J1I3K1Point,lowZeroSeedP2J1I3K1Point]
  · convert lowZeroCoefficientsP2J1I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I3Coefficient,lowZeroSeedP2J1I3K1Point,lowZeroSeedP2J1I3K2Point]
  · convert lowZeroCoefficientsP2J1I3K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I3Coefficient,lowZeroSeedP2J1I3K1Point,lowZeroSeedP2J1I3K3Point]
  · convert lowZeroCoefficientsP2J1I3K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I3Coefficient,lowZeroSeedP2J1I3K1Point,lowZeroSeedP2J1I3K4Point]
  · convert lowZeroCoefficientsP2J1I3K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I3Coefficient,lowZeroSeedP2J1I3K1Point,lowZeroSeedP2J1I3K5Point]

def lowZeroPanelP2J1I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP2J1I3Coefficient

theorem lowZeroPanelP2J1I3Value_eq : lowZeroPanelP2J1I3Value=(1125066789797377789462875048852092146089850126623841744069484995852950243215399024290765783144195917997812432859901051140479287577109007897103493400859064286480764689382638494891763787:ℚ)/1147207811785299338979300095700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J1I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J1I3K1Point (theta48PanelCenter 1 3)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP2J1I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J1I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J1I3K1Point (theta48PanelCenter 1 3)
    ((1:ℚ)/8) lowZeroPanelP2J1I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J1I3Value,theta48PanelHalfWidth]

end ReciprocalXi
