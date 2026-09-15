import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I7K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I7K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I7K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J1I7K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J1I7Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J1I7K1State n
  | 1 => lowZeroCoefficientsP2J1I7K2State n
  | 2 => lowZeroCoefficientsP2J1I7K3State n
  | 3 => lowZeroCoefficientsP2J1I7K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J1I7_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J1I7Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J1I7K1Point)
        (theta48PanelCenter 1 7:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J1I7K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I7Coefficient,lowZeroSeedP2J1I7K1Point,lowZeroSeedP2J1I7K1Point]
  · convert lowZeroCoefficientsP2J1I7K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I7Coefficient,lowZeroSeedP2J1I7K1Point,lowZeroSeedP2J1I7K2Point]
  · convert lowZeroCoefficientsP2J1I7K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I7Coefficient,lowZeroSeedP2J1I7K1Point,lowZeroSeedP2J1I7K3Point]
  · convert lowZeroCoefficientsP2J1I7K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J1I7Coefficient,lowZeroSeedP2J1I7K1Point,lowZeroSeedP2J1I7K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J1I7K1Point
        (theta48PanelCenter 1 7) (theta48PanelHalfWidth 1) 5 n
        (by norm_num [lowZeroSeedP2J1I7K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J1I7Coefficient]

def lowZeroPanelP2J1I7Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP2J1I7Coefficient

theorem lowZeroPanelP2J1I7Value_eq : lowZeroPanelP2J1I7Value=(-98972831509420165512019249202621676127562911961394012300062835397159546018252683799305038746644637359434863164826877080682972097056808662251748217658601224170767293052848415854142886473:ℚ)/2027116203424623931976423269101900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J1I7_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J1I7K1Point (theta48PanelCenter 1 7)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP2J1I7Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J1I7_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J1I7K1Point (theta48PanelCenter 1 7)
    ((1:ℚ)/8) lowZeroPanelP2J1I7Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J1I7Value,theta48PanelHalfWidth]

end ReciprocalXi
