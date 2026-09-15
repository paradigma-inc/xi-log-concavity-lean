import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I5K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I5K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I5K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I5K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I5K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J0I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J0I5K1State n
  | 1 => lowZeroCoefficientsP1J0I5K2State n
  | 2 => lowZeroCoefficientsP1J0I5K3State n
  | 3 => lowZeroCoefficientsP1J0I5K4State n
  | 4 => lowZeroCoefficientsP1J0I5K5State n
  | _ => (0,0)

theorem lowZeroPanelP1J0I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J0I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J0I5K1Point)
        (theta48PanelCenter 0 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J0I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I5Coefficient,lowZeroSeedP1J0I5K1Point,lowZeroSeedP1J0I5K1Point]
  · convert lowZeroCoefficientsP1J0I5K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I5Coefficient,lowZeroSeedP1J0I5K1Point,lowZeroSeedP1J0I5K2Point]
  · convert lowZeroCoefficientsP1J0I5K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I5Coefficient,lowZeroSeedP1J0I5K1Point,lowZeroSeedP1J0I5K3Point]
  · convert lowZeroCoefficientsP1J0I5K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I5Coefficient,lowZeroSeedP1J0I5K1Point,lowZeroSeedP1J0I5K4Point]
  · convert lowZeroCoefficientsP1J0I5K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I5Coefficient,lowZeroSeedP1J0I5K1Point,lowZeroSeedP1J0I5K5Point]

def lowZeroPanelP1J0I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP1J0I5Coefficient

theorem lowZeroPanelP1J0I5Value_eq : lowZeroPanelP1J0I5Value=(-1522127810409974178548879766928958171810420373554098089779593598221669819434388599518006196962366642319078908156252648373388770226506280224808317036552853392410045774933920232203049289037:ℚ)/2108504476206182579546934958500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J0I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J0I5K1Point (theta48PanelCenter 0 5)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP1J0I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J0I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J0I5K1Point (theta48PanelCenter 0 5)
    ((1:ℚ)/16) lowZeroPanelP1J0I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J0I5Value,theta48PanelHalfWidth]

end ReciprocalXi
