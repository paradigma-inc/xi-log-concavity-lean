import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J3I1K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J3I1K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J3I1Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J3I1K1State n
  | 1 => lowZeroCoefficientsP2J3I1K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J3I1_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J3I1Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J3I1K1Point)
        (theta48PanelCenter 3 1:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J3I1K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J3I1Coefficient,lowZeroSeedP2J3I1K1Point,lowZeroSeedP2J3I1K1Point]
  · convert lowZeroCoefficientsP2J3I1K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J3I1Coefficient,lowZeroSeedP2J3I1K1Point,lowZeroSeedP2J3I1K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I1K1Point
        (theta48PanelCenter 3 1) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP2J3I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I1Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I1K1Point
        (theta48PanelCenter 3 1) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP2J3I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I1Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I1K1Point
        (theta48PanelCenter 3 1) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP2J3I1K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I1Coefficient]

def lowZeroPanelP2J3I1Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP2J3I1Coefficient

theorem lowZeroPanelP2J3I1Value_eq : lowZeroPanelP2J3I1Value=(-4009520246744708663983687421485352989308145430615639593902081498162288757586017340253376859889553997349625368820956647645969987157584324302744472640384655447885004930816822094949:ℚ)/422315875713463319161754847729562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J3I1_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J3I1K1Point (theta48PanelCenter 3 1)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP2J3I1Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J3I1_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J3I1K1Point (theta48PanelCenter 3 1)
    ((1:ℚ)/2) lowZeroPanelP2J3I1Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J3I1Value,theta48PanelHalfWidth]

end ReciprocalXi
