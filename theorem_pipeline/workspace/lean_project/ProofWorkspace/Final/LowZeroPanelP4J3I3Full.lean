import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J3I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J3I3K2Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J3I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J3I3K1State n
  | 1 => lowZeroCoefficientsP4J3I3K2State n
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J3I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J3I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J3I3K1Point)
        (theta48PanelCenter 3 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 3) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J3I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J3I3Coefficient,lowZeroSeedP4J3I3K1Point,lowZeroSeedP4J3I3K1Point]
  · convert lowZeroCoefficientsP4J3I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J3I3Coefficient,lowZeroSeedP4J3I3K1Point,lowZeroSeedP4J3I3K2Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 3 n
        (by norm_num [lowZeroSeedP4J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 4 n
        (by norm_num [lowZeroSeedP4J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J3I3K1Point
        (theta48PanelCenter 3 3) (theta48PanelHalfWidth 3) 5 n
        (by norm_num [lowZeroSeedP4J3I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J3I3Coefficient]

def lowZeroPanelP4J3I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/2) lowZeroPanelP4J3I3Coefficient

theorem lowZeroPanelP4J3I3Value_eq : lowZeroPanelP4J3I3Value=(11264146638873123881033467693682918689003672098403724724672547639362691416811986878973705797169234608120960375048522028889440249509488981567922047751879303395499048727414104747:ℚ)/281543917142308879441169898486375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J3I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J3I3K1Point (theta48PanelCenter 3 3)
      (theta48PanelHalfWidth 3) 80-(lowZeroPanelP4J3I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J3I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J3I3K1Point (theta48PanelCenter 3 3)
    ((1:ℚ)/2) lowZeroPanelP4J3I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J3I3Value,theta48PanelHalfWidth]

end ReciprocalXi
