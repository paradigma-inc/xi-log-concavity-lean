import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I7K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I7K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J1I7K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J1I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J1I7K1State n
  | 1 => lowZeroCoefficientsP3J1I7K2State n
  | 2 => lowZeroCoefficientsP3J1I7K3State n
  | 3 => lowZeroCoefficientsP3J1I7K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J1I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J1I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J1I7K1Point)
        (theta48PanelCenter 1 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J1I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I7Coefficient,lowZeroSeedP3J1I7K1Point,lowZeroSeedP3J1I7K1Point]
  · convert lowZeroCoefficientsP3J1I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I7Coefficient,lowZeroSeedP3J1I7K1Point,lowZeroSeedP3J1I7K2Point]
  · convert lowZeroCoefficientsP3J1I7K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I7Coefficient,lowZeroSeedP3J1I7K1Point,lowZeroSeedP3J1I7K3Point]
  · convert lowZeroCoefficientsP3J1I7K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J1I7Coefficient,lowZeroSeedP3J1I7K1Point,lowZeroSeedP3J1I7K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J1I7K1Point
        (theta48PanelCenter 1 7) (theta48PanelHalfWidth 1) 5 n
        (by norm_num [lowZeroSeedP3J1I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J1I7Coefficient]

def lowZeroPanelP3J1I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP3J1I7Coefficient

theorem lowZeroPanelP3J1I7Value_eq : lowZeroPanelP3J1I7Value=(-317220613812244120230830927014205295469613071658998756342463566151744223281979781976419464557236146287483286250671470272604355152420996663057305491320609981192079363825212515519548331:ℚ)/6497167318668666448642382272762500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J1I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J1I7K1Point (theta48PanelCenter 1 7)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP3J1I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J1I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J1I7K1Point (theta48PanelCenter 1 7)
    ((1:ℚ)/8) lowZeroPanelP3J1I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J1I7Value,theta48PanelHalfWidth]

end ReciprocalXi
