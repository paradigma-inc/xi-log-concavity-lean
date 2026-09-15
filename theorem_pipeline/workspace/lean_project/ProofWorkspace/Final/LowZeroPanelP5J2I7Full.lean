import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I7K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP5J2I7K3Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP5J2I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP5J2I7K1State n
  | 1 => lowZeroCoefficientsP5J2I7K2State n
  | 2 => lowZeroCoefficientsP5J2I7K3State n
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP5J2I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP5J2I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP5J2I7K1Point)
        (theta48PanelCenter 2 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP5J2I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I7Coefficient,lowZeroSeedP5J2I7K1Point,lowZeroSeedP5J2I7K1Point]
  · convert lowZeroCoefficientsP5J2I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I7Coefficient,lowZeroSeedP5J2I7K1Point,lowZeroSeedP5J2I7K2Point]
  · convert lowZeroCoefficientsP5J2I7K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP5J2I7Coefficient,lowZeroSeedP5J2I7K1Point,lowZeroSeedP5J2I7K3Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J2I7K1Point
        (theta48PanelCenter 2 7) (theta48PanelHalfWidth 2) 4 n
        (by norm_num [lowZeroSeedP5J2I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J2I7Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP5J2I7K1Point
        (theta48PanelCenter 2 7) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP5J2I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP5J2I7Coefficient]

def lowZeroPanelP5J2I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP5J2I7Coefficient

theorem lowZeroPanelP5J2I7Value_eq : lowZeroPanelP5J2I7Value=(11273811312092662943988591233164719345315767021741792034801768583620959470051486133275809837864374837051944158839317944948466128081791406888387629496701411610729180862863582011389:ℚ)/1935748857357356695928593648875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP5J2I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP5J2I7K1Point (theta48PanelCenter 2 7)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP5J2I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP5J2I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP5J2I7K1Point (theta48PanelCenter 2 7)
    ((1:ℚ)/4) lowZeroPanelP5J2I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP5J2I7Value,theta48PanelHalfWidth]

end ReciprocalXi
