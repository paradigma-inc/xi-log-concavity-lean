import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I3K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I3K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I3K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J1I3K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J1I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J1I3K1State n
  | 1 => lowZeroCoefficientsP5J1I3K2State n
  | 2 => lowZeroCoefficientsP5J1I3K3State n
  | 3 => lowZeroCoefficientsP5J1I3K4State n
  | 4 => lowZeroCoefficientsP5J1I3K5State n
  | _ => (0,0)

theorem lowZeroPanelP5J1I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J1I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J1I3K1Point)
        (theta48PanelCenter 1 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J1I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I3Coefficient,lowZeroSeedP5J1I3K1Point,lowZeroSeedP5J1I3K1Point]
  · convert lowZeroCoefficientsP5J1I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I3Coefficient,lowZeroSeedP5J1I3K1Point,lowZeroSeedP5J1I3K2Point]
  · convert lowZeroCoefficientsP5J1I3K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I3Coefficient,lowZeroSeedP5J1I3K1Point,lowZeroSeedP5J1I3K3Point]
  · convert lowZeroCoefficientsP5J1I3K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I3Coefficient,lowZeroSeedP5J1I3K1Point,lowZeroSeedP5J1I3K4Point]
  · convert lowZeroCoefficientsP5J1I3K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J1I3Coefficient,lowZeroSeedP5J1I3K1Point,lowZeroSeedP5J1I3K5Point]

def lowZeroPanelP5J1I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP5J1I3Coefficient

theorem lowZeroPanelP5J1I3Value_eq : lowZeroPanelP5J1I3Value=(228487459227840601703841993666603317886364096767871282800057138787637369288853341243646929972265046550657471356633360552875803684121483900318738859837010482116828191052585270385397198090569:ℚ)/10135581017123119659882116345509500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J1I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J1I3K1Point (theta48PanelCenter 1 3)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP5J1I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J1I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J1I3K1Point (theta48PanelCenter 1 3)
    ((1:ℚ)/8) lowZeroPanelP5J1I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J1I3Value,theta48PanelHalfWidth]

end ReciprocalXi
