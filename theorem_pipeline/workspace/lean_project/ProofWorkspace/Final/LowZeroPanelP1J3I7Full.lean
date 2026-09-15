import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J3I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J3I7K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J3I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J3I7K1State n
  | 1 => lowZeroCoefficientsP1J3I7K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP1J3I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J3I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J3I7K1Point)
        (theta48PanelCenter 3 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J3I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J3I7Coefficient,lowZeroSeedP1J3I7K1Point,lowZeroSeedP1J3I7K1Point]
  · convert lowZeroCoefficientsP1J3I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J3I7Coefficient,lowZeroSeedP1J3I7K1Point,lowZeroSeedP1J3I7K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP1J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP1J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP1J3I7K1Point
        (theta48PanelCenter 3 7) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP1J3I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP1J3I7Coefficient]

def lowZeroPanelP1J3I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP1J3I7Coefficient

theorem lowZeroPanelP1J3I7Value_eq : lowZeroPanelP1J3I7Value=(10731135582521341879825669797597741452404015053319823392034364400387348594809296724782552656460478507417893611936484030924398055039554038518388075321107147555962855299677:ℚ)/43687849211737584740871191144437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J3I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J3I7K1Point (theta48PanelCenter 3 7)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP1J3I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J3I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J3I7K1Point (theta48PanelCenter 3 7)
    ((1:ℚ)/2) lowZeroPanelP1J3I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J3I7Value,theta48PanelHalfWidth]

end ReciprocalXi
