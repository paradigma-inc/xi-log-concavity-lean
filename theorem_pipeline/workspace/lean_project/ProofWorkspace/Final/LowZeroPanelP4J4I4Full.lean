import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J4I4K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J4I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J4I4K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J4I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J4I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J4I4K1Point)
        (theta48PanelCenter 4 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J4I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J4I4Coefficient,lowZeroSeedP4J4I4K1Point,lowZeroSeedP4J4I4K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP4J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP4J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP4J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I4Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J4I4K1Point
        (theta48PanelCenter 4 4) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP4J4I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J4I4Coefficient]

def lowZeroPanelP4J4I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP4J4I4Coefficient

theorem lowZeroPanelP4J4I4Value_eq : lowZeroPanelP4J4I4Value=(-208235449103874322137150188722441708778996111126938031750672791366949838788359106697450041195820674637397343061775953422651555525619266632992875617722247663:ℚ)/3414953172885148133383462380562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J4I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J4I4K1Point (theta48PanelCenter 4 4)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP4J4I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J4I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J4I4K1Point (theta48PanelCenter 4 4)
    ((1:ℚ)/1) lowZeroPanelP4J4I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J4I4Value,theta48PanelHalfWidth]

end ReciprocalXi
