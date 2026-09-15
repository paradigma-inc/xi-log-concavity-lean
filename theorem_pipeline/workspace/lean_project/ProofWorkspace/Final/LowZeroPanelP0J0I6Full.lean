import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I6K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I6K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I6K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I6K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J0I6K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J0I6Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J0I6K1State n
  | 1 => lowZeroCoefficientsP0J0I6K2State n
  | 2 => lowZeroCoefficientsP0J0I6K3State n
  | 3 => lowZeroCoefficientsP0J0I6K4State n
  | 4 => lowZeroCoefficientsP0J0I6K5State n
  | _ => (0,0)

theorem lowZeroPanelP0J0I6_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J0I6Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J0I6K1Point)
        (theta48PanelCenter 0 6:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J0I6K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I6Coefficient,lowZeroSeedP0J0I6K1Point,lowZeroSeedP0J0I6K1Point]
  · convert lowZeroCoefficientsP0J0I6K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I6Coefficient,lowZeroSeedP0J0I6K1Point,lowZeroSeedP0J0I6K2Point]
  · convert lowZeroCoefficientsP0J0I6K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I6Coefficient,lowZeroSeedP0J0I6K1Point,lowZeroSeedP0J0I6K3Point]
  · convert lowZeroCoefficientsP0J0I6K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I6Coefficient,lowZeroSeedP0J0I6K1Point,lowZeroSeedP0J0I6K4Point]
  · convert lowZeroCoefficientsP0J0I6K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J0I6Coefficient,lowZeroSeedP0J0I6K1Point,lowZeroSeedP0J0I6K5Point]

def lowZeroPanelP0J0I6Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP0J0I6Coefficient

theorem lowZeroPanelP0J0I6Value_eq : lowZeroPanelP0J0I6Value=(-1375211038076897978706369496421310805220199712666591931287856567025017149424963905345939061209578007889598030052925955513246494351702621171340125091223137061516582928747478324892564772273051:ℚ)/5067790508561559829941058172754750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J0I6_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J0I6K1Point (theta48PanelCenter 0 6)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP0J0I6Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J0I6_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J0I6K1Point (theta48PanelCenter 0 6)
    ((1:ℚ)/16) lowZeroPanelP0J0I6Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J0I6Value,theta48PanelHalfWidth]

end ReciprocalXi
