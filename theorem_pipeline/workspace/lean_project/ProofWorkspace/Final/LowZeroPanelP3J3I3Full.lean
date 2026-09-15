import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J3I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J3I3K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J3I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J3I3K1State n
  | 1 => lowZeroCoefficientsP3J3I3K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J3I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J3I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J3I3K1Point)
        (theta48PanelCenter 3 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J3I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J3I3Coefficient,lowZeroSeedP3J3I3K1Point,lowZeroSeedP3J3I3K1Point]
  · convert lowZeroCoefficientsP3J3I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J3I3Coefficient,lowZeroSeedP3J3I3K1Point,lowZeroSeedP3J3I3K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP3J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP3J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP3J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J3I3Coefficient]

def lowZeroPanelP3J3I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP3J3I3Coefficient

theorem lowZeroPanelP3J3I3Value_eq : lowZeroPanelP3J3I3Value=(5190107065024528465143200976002144438140032325772992417847639873350730843603095989040412616546824797466708389684405300429256387163135274774188360617326979437817455077977821559:ℚ)/57588528506381361703875661054031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J3I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J3I3K1Point (theta48PanelCenter 3 3)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP3J3I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J3I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J3I3K1Point (theta48PanelCenter 3 3)
    ((1:ℚ)/2) lowZeroPanelP3J3I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J3I3Value,theta48PanelHalfWidth]

end ReciprocalXi
