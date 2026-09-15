import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I7K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I7K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I7K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I7K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J0I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J0I7K1State n
  | 1 => lowZeroCoefficientsP1J0I7K2State n
  | 2 => lowZeroCoefficientsP1J0I7K3State n
  | 3 => lowZeroCoefficientsP1J0I7K4State n
  | 4 => lowZeroCoefficientsP1J0I7K5State n
  | _ => (0,0)

theorem lowZeroPanelP1J0I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J0I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J0I7K1Point)
        (theta48PanelCenter 0 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J0I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I7Coefficient,lowZeroSeedP1J0I7K1Point,lowZeroSeedP1J0I7K1Point]
  · convert lowZeroCoefficientsP1J0I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I7Coefficient,lowZeroSeedP1J0I7K1Point,lowZeroSeedP1J0I7K2Point]
  · convert lowZeroCoefficientsP1J0I7K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I7Coefficient,lowZeroSeedP1J0I7K1Point,lowZeroSeedP1J0I7K3Point]
  · convert lowZeroCoefficientsP1J0I7K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I7Coefficient,lowZeroSeedP1J0I7K1Point,lowZeroSeedP1J0I7K4Point]
  · convert lowZeroCoefficientsP1J0I7K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I7Coefficient,lowZeroSeedP1J0I7K1Point,lowZeroSeedP1J0I7K5Point]

def lowZeroPanelP1J0I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP1J0I7Coefficient

theorem lowZeroPanelP1J0I7Value_eq : lowZeroPanelP1J0I7Value=(-98164596049461667209476179365489486839202958895214946388531502350157545818436981723514716689366232100625736696577943542751335445210151511583646308103586876714316593670533372516198845843023:ℚ)/5067790508561559829941058172754750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J0I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J0I7K1Point (theta48PanelCenter 0 7)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP1J0I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J0I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J0I7K1Point (theta48PanelCenter 0 7)
    ((1:ℚ)/16) lowZeroPanelP1J0I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J0I7Value,theta48PanelHalfWidth]

end ReciprocalXi
