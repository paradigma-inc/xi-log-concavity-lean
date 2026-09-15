import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J2I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J2I3K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP3J2I3K3Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J2I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J2I3K1State n
  | 1 => lowZeroCoefficientsP3J2I3K2State n
  | 2 => lowZeroCoefficientsP3J2I3K3State n
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J2I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J2I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J2I3K1Point)
        (theta48PanelCenter 2 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 2) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J2I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J2I3Coefficient,lowZeroSeedP3J2I3K1Point,lowZeroSeedP3J2I3K1Point]
  · convert lowZeroCoefficientsP3J2I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J2I3Coefficient,lowZeroSeedP3J2I3K1Point,lowZeroSeedP3J2I3K2Point]
  · convert lowZeroCoefficientsP3J2I3K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J2I3Coefficient,lowZeroSeedP3J2I3K1Point,lowZeroSeedP3J2I3K3Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J2I3K1Point
        (theta48PanelCenter 2 3) (theta48PanelHalfWidth 2) 4 n
        (by norm_num [lowZeroSeedP3J2I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J2I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J2I3K1Point
        (theta48PanelCenter 2 3) (theta48PanelHalfWidth 2) 5 n
        (by norm_num [lowZeroSeedP3J2I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J2I3Coefficient]

def lowZeroPanelP3J2I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/4) lowZeroPanelP3J2I3Coefficient

theorem lowZeroPanelP3J2I3Value_eq : lowZeroPanelP3J2I3Value=(626454455103356659695971569612482924173194414794979795599115637573460894896865444596615597345466313459727996022397273576484193349887443683237620118449334395263351698250664535638584627:ℚ)/180992518162912851069323506169812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J2I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J2I3K1Point (theta48PanelCenter 2 3)
      (theta48PanelHalfWidth 2) 80-(lowZeroPanelP3J2I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J2I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J2I3K1Point (theta48PanelCenter 2 3)
    ((1:ℚ)/4) lowZeroPanelP3J2I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J2I3Value,theta48PanelHalfWidth]

end ReciprocalXi
