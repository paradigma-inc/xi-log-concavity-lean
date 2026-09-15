import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J3I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J3I0K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J3I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J3I0K1State n
  | 1 => lowZeroCoefficientsP2J3I0K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J3I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J3I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J3I0K1Point)
        (theta48PanelCenter 3 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J3I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J3I0Coefficient,lowZeroSeedP2J3I0K1Point,lowZeroSeedP2J3I0K1Point]
  · convert lowZeroCoefficientsP2J3I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J3I0Coefficient,lowZeroSeedP2J3I0K1Point,lowZeroSeedP2J3I0K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I0K1Point
        (theta48PanelCenter 3 0) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP2J3I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I0Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I0K1Point
        (theta48PanelCenter 3 0) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP2J3I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I0Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I0K1Point
        (theta48PanelCenter 3 0) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP2J3I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I0Coefficient]

def lowZeroPanelP2J3I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP2J3I0Coefficient

theorem lowZeroPanelP2J3I0Value_eq : lowZeroPanelP2J3I0Value=(-3616132723967487383358710571250117958946390499455768505907375619244099195858827827141843421001191110435384516721947589787389298303332356416260489017058186399694635217723442655635603:ℚ)/2533895254280779914970529086377375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J3I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J3I0K1Point (theta48PanelCenter 3 0)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP2J3I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J3I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J3I0K1Point (theta48PanelCenter 3 0)
    ((1:ℚ)/2) lowZeroPanelP2J3I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J3I0Value,theta48PanelHalfWidth]

end ReciprocalXi
