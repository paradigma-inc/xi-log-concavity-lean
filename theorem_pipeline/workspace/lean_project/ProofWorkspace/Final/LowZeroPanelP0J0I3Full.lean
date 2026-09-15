import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I3K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I3K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I3K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I3K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J0I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J0I3K1State n
  | 1 => lowZeroCoefficientsP0J0I3K2State n
  | 2 => lowZeroCoefficientsP0J0I3K3State n
  | 3 => lowZeroCoefficientsP0J0I3K4State n
  | 4 => lowZeroCoefficientsP0J0I3K5State n
  | _ => (0,0)

theorem lowZeroPanelP0J0I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J0I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J0I3K1Point)
        (theta48PanelCenter 0 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J0I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I3Coefficient,lowZeroSeedP0J0I3K1Point,lowZeroSeedP0J0I3K1Point]
  · convert lowZeroCoefficientsP0J0I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I3Coefficient,lowZeroSeedP0J0I3K1Point,lowZeroSeedP0J0I3K2Point]
  · convert lowZeroCoefficientsP0J0I3K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I3Coefficient,lowZeroSeedP0J0I3K1Point,lowZeroSeedP0J0I3K3Point]
  · convert lowZeroCoefficientsP0J0I3K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I3Coefficient,lowZeroSeedP0J0I3K1Point,lowZeroSeedP0J0I3K4Point]
  · convert lowZeroCoefficientsP0J0I3K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I3Coefficient,lowZeroSeedP0J0I3K1Point,lowZeroSeedP0J0I3K5Point]

def lowZeroPanelP0J0I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP0J0I3Coefficient

theorem lowZeroPanelP0J0I3Value_eq : lowZeroPanelP0J0I3Value=(-1190901831296803303134014066138748168322718703600996765016254497220414930822765392722445624223940299671433283752004223250149547789446551658115112169496667894302827701396184651329269542456617:ℚ)/699005587387801355853939058311000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J0I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J0I3K1Point (theta48PanelCenter 0 3)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP0J0I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J0I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J0I3K1Point (theta48PanelCenter 0 3)
    ((1:ℚ)/16) lowZeroPanelP0J0I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J0I3Value,theta48PanelHalfWidth]

end ReciprocalXi
