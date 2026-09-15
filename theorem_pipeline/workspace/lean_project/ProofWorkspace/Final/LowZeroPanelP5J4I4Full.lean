import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J4I4K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J4I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J4I4K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP5J4I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J4I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J4I4K1Point)
        (theta48PanelCenter 4 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J4I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J4I4Coefficient,lowZeroSeedP5J4I4K1Point,lowZeroSeedP5J4I4K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP5J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP5J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP5J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP5J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J4I4Coefficient]

def lowZeroPanelP5J4I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP5J4I4Coefficient

theorem lowZeroPanelP5J4I4Value_eq : lowZeroPanelP5J4I4Value=(-48044372896478466114976815932455301863442414464579281916003359671935962538383548094397747351849790865378398379331466487733165826334158153947858327090627541:ℚ)/787902753196759923809244118898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J4I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J4I4K1Point (theta48PanelCenter 4 4)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP5J4I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J4I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J4I4K1Point (theta48PanelCenter 4 4)
    ((1:ℚ)/1) lowZeroPanelP5J4I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J4I4Value,theta48PanelHalfWidth]

end ReciprocalXi
