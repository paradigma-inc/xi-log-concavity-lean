import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I4K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I4K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I4K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP4J1I4K4Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP4J1I4Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP4J1I4K1State n
  | 1 => lowZeroCoefficientsP4J1I4K2State n
  | 2 => lowZeroCoefficientsP4J1I4K3State n
  | 3 => lowZeroCoefficientsP4J1I4K4State n
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP4J1I4_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP4J1I4Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP4J1I4K1Point)
        (theta48PanelCenter 1 4:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 1) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP4J1I4K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I4Coefficient,lowZeroSeedP4J1I4K1Point,lowZeroSeedP4J1I4K1Point]
  · convert lowZeroCoefficientsP4J1I4K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I4Coefficient,lowZeroSeedP4J1I4K1Point,lowZeroSeedP4J1I4K2Point]
  · convert lowZeroCoefficientsP4J1I4K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I4Coefficient,lowZeroSeedP4J1I4K1Point,lowZeroSeedP4J1I4K3Point]
  · convert lowZeroCoefficientsP4J1I4K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP4J1I4Coefficient,lowZeroSeedP4J1I4K1Point,lowZeroSeedP4J1I4K4Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP4J1I4K1Point
        (theta48PanelCenter 1 4) (theta48PanelHalfWidth 1) 5 n
        (by norm_num [lowZeroSeedP4J1I4K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP4J1I4Coefficient]

def lowZeroPanelP4J1I4Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/8) lowZeroPanelP4J1I4Coefficient

theorem lowZeroPanelP4J1I4Value_eq : lowZeroPanelP4J1I4Value=(-91510620203866057493986198109596529844156911079018980316008317677474536360569105529571553843273835102691836374293625307211613346448375900872518907229591878706783211930694063508462702493:ℚ)/211157937856731659580877423864781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP4J1I4_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP4J1I4K1Point (theta48PanelCenter 1 4)
      (theta48PanelHalfWidth 1) 80-(lowZeroPanelP4J1I4Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP4J1I4_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP4J1I4K1Point (theta48PanelCenter 1 4)
    ((1:ℚ)/8) lowZeroPanelP4J1I4Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP4J1I4Value,theta48PanelHalfWidth]

end ReciprocalXi
