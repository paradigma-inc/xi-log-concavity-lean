import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J4I4K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J4I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J4I4K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP1J4I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J4I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J4I4K1Point)
        (theta48PanelCenter 4 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J4I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J4I4Coefficient,lowZeroSeedP1J4I4K1Point,lowZeroSeedP1J4I4K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP1J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP1J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP1J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP1J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J4I4Coefficient]

def lowZeroPanelP1J4I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP1J4I4Coefficient

theorem lowZeroPanelP1J4I4Value_eq : lowZeroPanelP1J4I4Value=(-8588416456272978383166316393504044461089861601528298147448060061766676977294348924869614054933385594086414713321421078294037569017461746281266845061499650533:ℚ)/97457509780029996729635734091437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J4I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J4I4K1Point (theta48PanelCenter 4 4)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP1J4I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J4I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J4I4K1Point (theta48PanelCenter 4 4)
    ((1:ℚ)/1) lowZeroPanelP1J4I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J4I4Value,theta48PanelHalfWidth]

end ReciprocalXi
