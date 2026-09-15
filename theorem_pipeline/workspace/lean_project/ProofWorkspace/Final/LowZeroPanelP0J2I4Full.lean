import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP0J2I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J2I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP0J2I4K3Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP0J2I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP0J2I4K1State n
  | 1 => lowZeroCoefficientsP0J2I4K2State n
  | 2 => lowZeroCoefficientsP0J2I4K3State n
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP0J2I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP0J2I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP0J2I4K1Point)
        (theta48PanelCenter 2 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP0J2I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J2I4Coefficient,lowZeroSeedP0J2I4K1Point,lowZeroSeedP0J2I4K1Point]
  · convert lowZeroCoefficientsP0J2I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J2I4Coefficient,lowZeroSeedP0J2I4K1Point,lowZeroSeedP0J2I4K2Point]
  · convert lowZeroCoefficientsP0J2I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP0J2I4Coefficient,lowZeroSeedP0J2I4K1Point,lowZeroSeedP0J2I4K3Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J2I4K1Point
        (theta48PanelCenter 2 4) (theta48PanelHalfWidth 2) 4 n
        (by norm_num [lowZeroSeedP0J2I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J2I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP0J2I4K1Point
        (theta48PanelCenter 2 4) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP0J2I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP0J2I4Coefficient]

def lowZeroPanelP0J2I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP0J2I4Coefficient

theorem lowZeroPanelP0J2I4Value_eq : lowZeroPanelP0J2I4Value=(665835987269890521790846933070982599065463642220510179485240779179981431475279430200668575092627898950472864417570134281471827192675893438421456383864836259960269810979845190005758493:ℚ)/844631751426926638323509695459125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP0J2I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP0J2I4K1Point (theta48PanelCenter 2 4)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP0J2I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP0J2I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP0J2I4K1Point (theta48PanelCenter 2 4)
    ((1:ℚ)/4) lowZeroPanelP0J2I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP0J2I4Value,theta48PanelHalfWidth]

end ReciprocalXi
