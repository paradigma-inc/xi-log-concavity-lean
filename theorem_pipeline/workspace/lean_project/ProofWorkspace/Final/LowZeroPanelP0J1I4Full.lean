import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I4K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J1I4K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J1I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J1I4K1State n
  | 1 => lowZeroCoefficientsP0J1I4K2State n
  | 2 => lowZeroCoefficientsP0J1I4K3State n
  | 3 => lowZeroCoefficientsP0J1I4K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP0J1I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J1I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J1I4K1Point)
        (theta48PanelCenter 1 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J1I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I4Coefficient,lowZeroSeedP0J1I4K1Point,lowZeroSeedP0J1I4K1Point]
  · convert lowZeroCoefficientsP0J1I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I4Coefficient,lowZeroSeedP0J1I4K1Point,lowZeroSeedP0J1I4K2Point]
  · convert lowZeroCoefficientsP0J1I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I4Coefficient,lowZeroSeedP0J1I4K1Point,lowZeroSeedP0J1I4K3Point]
  · convert lowZeroCoefficientsP0J1I4K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J1I4Coefficient,lowZeroSeedP0J1I4K1Point,lowZeroSeedP0J1I4K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J1I4K1Point
        (theta48PanelCenter 1 4) (theta48PanelHalfWidth 1) 5 n
        (by norm_num [lowZeroSeedP0J1I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J1I4Coefficient]

def lowZeroPanelP0J1I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP0J1I4Coefficient

theorem lowZeroPanelP0J1I4Value_eq : lowZeroPanelP0J1I4Value=(-2339973352420021952377521979906234787257561218718789943966329421558613793761217372257677457344984483621146402276871365767133430131560540142724095067123947379122845934407883355429523256169:ℚ)/1266947627140389957485264543188687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J1I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J1I4K1Point (theta48PanelCenter 1 4)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP0J1I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J1I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J1I4K1Point (theta48PanelCenter 1 4)
    ((1:ℚ)/8) lowZeroPanelP0J1I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J1I4Value,theta48PanelHalfWidth]

end ReciprocalXi
