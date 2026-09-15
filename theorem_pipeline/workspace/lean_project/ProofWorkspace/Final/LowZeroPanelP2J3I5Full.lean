import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J3I5K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J3I5K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J3I5Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J3I5K1State n
  | 1 => lowZeroCoefficientsP2J3I5K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J3I5_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J3I5Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J3I5K1Point)
        (theta48PanelCenter 3 5:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J3I5K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J3I5Coefficient,lowZeroSeedP2J3I5K1Point,lowZeroSeedP2J3I5K1Point]
  · convert lowZeroCoefficientsP2J3I5K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J3I5Coefficient,lowZeroSeedP2J3I5K1Point,lowZeroSeedP2J3I5K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I5K1Point
        (theta48PanelCenter 3 5) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP2J3I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I5Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I5K1Point
        (theta48PanelCenter 3 5) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP2J3I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I5Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J3I5K1Point
        (theta48PanelCenter 3 5) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP2J3I5K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J3I5Coefficient]

def lowZeroPanelP2J3I5Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP2J3I5Coefficient

theorem lowZeroPanelP2J3I5Value_eq : lowZeroPanelP2J3I5Value=(-6975232268035677092738441281737516250803867179176766329227261189209376835942395144775170559218975789308383381158806127172767414252651905859628861044816153914943703268127137:ℚ)/97457509780029996729635734091437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J3I5_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J3I5K1Point (theta48PanelCenter 3 5)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP2J3I5Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J3I5_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J3I5K1Point (theta48PanelCenter 3 5)
    ((1:ℚ)/2) lowZeroPanelP2J3I5Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J3I5Value,theta48PanelHalfWidth]

end ReciprocalXi
