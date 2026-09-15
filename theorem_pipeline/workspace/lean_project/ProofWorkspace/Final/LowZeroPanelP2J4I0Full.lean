import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP2J4I0K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP2J4I0K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP2J4I0Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP2J4I0K1State n
  | 1 => lowZeroCoefficientsP2J4I0K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP2J4I0_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP2J4I0Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP2J4I0K1Point)
        (theta48PanelCenter 4 0:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP2J4I0K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J4I0Coefficient,lowZeroSeedP2J4I0K1Point,lowZeroSeedP2J4I0K1Point]
  · convert lowZeroCoefficientsP2J4I0K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP2J4I0Coefficient,lowZeroSeedP2J4I0K1Point,lowZeroSeedP2J4I0K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J4I0K1Point
        (theta48PanelCenter 4 0) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP2J4I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J4I0Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J4I0K1Point
        (theta48PanelCenter 4 0) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP2J4I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J4I0Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP2J4I0K1Point
        (theta48PanelCenter 4 0) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP2J4I0K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP2J4I0Coefficient]

def lowZeroPanelP2J4I0Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP2J4I0Coefficient

theorem lowZeroPanelP2J4I0Value_eq : lowZeroPanelP2J4I0Value=(-248546695239773843915535352901705808148264107805976198055372876578651552602455158828640967198109663091678396312971174950863987565214535939193094064577503356384511617987:ℚ)/45248129540728212767330876542453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP2J4I0_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP2J4I0K1Point (theta48PanelCenter 4 0)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP2J4I0Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP2J4I0_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP2J4I0K1Point (theta48PanelCenter 4 0)
    ((1:ℚ)/1) lowZeroPanelP2J4I0Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP2J4I0Value,theta48PanelHalfWidth]

end ReciprocalXi
