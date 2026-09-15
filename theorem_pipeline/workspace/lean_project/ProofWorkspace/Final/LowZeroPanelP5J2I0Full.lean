import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I0K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I0K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I0K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J2I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J2I0K1State n
  | 1 => lowZeroCoefficientsP5J2I0K2State n
  | 2 => lowZeroCoefficientsP5J2I0K3State n
  | 3 => lowZeroCoefficientsP5J2I0K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP5J2I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J2I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J2I0K1Point)
        (theta48PanelCenter 2 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J2I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I0Coefficient,lowZeroSeedP5J2I0K1Point,lowZeroSeedP5J2I0K1Point]
  · convert lowZeroCoefficientsP5J2I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I0Coefficient,lowZeroSeedP5J2I0K1Point,lowZeroSeedP5J2I0K2Point]
  · convert lowZeroCoefficientsP5J2I0K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I0Coefficient,lowZeroSeedP5J2I0K1Point,lowZeroSeedP5J2I0K3Point]
  · convert lowZeroCoefficientsP5J2I0K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I0Coefficient,lowZeroSeedP5J2I0K1Point,lowZeroSeedP5J2I0K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J2I0K1Point
        (theta48PanelCenter 2 0) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP5J2I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J2I0Coefficient]

def lowZeroPanelP5J2I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP5J2I0Coefficient

theorem lowZeroPanelP5J2I0Value_eq : lowZeroPanelP5J2I0Value=(1578996887789030357530341711722513804148804626097327288698613375826117871754825931160224398997251846764470812068337358080121855240906014243678669042166160541753896747953606224724536763:ℚ)/4992897052770009684670993273650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J2I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J2I0K1Point (theta48PanelCenter 2 0)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP5J2I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J2I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J2I0K1Point (theta48PanelCenter 2 0)
    ((1:ℚ)/4) lowZeroPanelP5J2I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J2I0Value,theta48PanelHalfWidth]

end ReciprocalXi
