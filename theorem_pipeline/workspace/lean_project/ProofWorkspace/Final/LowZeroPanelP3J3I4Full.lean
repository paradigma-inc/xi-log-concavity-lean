import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J3I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J3I4K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J3I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J3I4K1State n
  | 1 => lowZeroCoefficientsP3J3I4K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J3I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J3I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J3I4K1Point)
        (theta48PanelCenter 3 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J3I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J3I4Coefficient,lowZeroSeedP3J3I4K1Point,lowZeroSeedP3J3I4K1Point]
  · convert lowZeroCoefficientsP3J3I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J3I4Coefficient,lowZeroSeedP3J3I4K1Point,lowZeroSeedP3J3I4K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I4K1Point
        (theta48PanelCenter 3 4) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP3J3I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I4K1Point
        (theta48PanelCenter 3 4) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP3J3I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I4K1Point
        (theta48PanelCenter 3 4) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP3J3I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I4Coefficient]

def lowZeroPanelP3J3I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP3J3I4Coefficient

theorem lowZeroPanelP3J3I4Value_eq : lowZeroPanelP3J3I4Value=(441813438341219246056269690230355016678976905494534619047140940326789198732140694463854236314396254847287096301837109265403521923913064388298505702101215417440292420860919:ℚ)/329719616692359130119782574675000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J3I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J3I4K1Point (theta48PanelCenter 3 4)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP3J3I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J3I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J3I4K1Point (theta48PanelCenter 3 4)
    ((1:ℚ)/2) lowZeroPanelP3J3I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J3I4Value,theta48PanelHalfWidth]

end ReciprocalXi
