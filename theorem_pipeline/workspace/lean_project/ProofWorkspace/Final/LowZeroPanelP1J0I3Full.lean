import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I3K1Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I3K2Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I3K3Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I3K4Full
import ProofWorkspace.Final.LowZeroCoefficientsP1J0I3K5Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP1J0I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP1J0I3K1State n
  | 1 => lowZeroCoefficientsP1J0I3K2State n
  | 2 => lowZeroCoefficientsP1J0I3K3State n
  | 3 => lowZeroCoefficientsP1J0I3K4State n
  | 4 => lowZeroCoefficientsP1J0I3K5State n
  | _ => (0,0)

theorem lowZeroPanelP1J0I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP1J0I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP1J0I3K1Point)
        (theta48PanelCenter 0 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 0) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP1J0I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I3Coefficient,lowZeroSeedP1J0I3K1Point,lowZeroSeedP1J0I3K1Point]
  · convert lowZeroCoefficientsP1J0I3K2_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I3Coefficient,lowZeroSeedP1J0I3K1Point,lowZeroSeedP1J0I3K2Point]
  · convert lowZeroCoefficientsP1J0I3K3_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I3Coefficient,lowZeroSeedP1J0I3K1Point,lowZeroSeedP1J0I3K3Point]
  · convert lowZeroCoefficientsP1J0I3K4_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I3Coefficient,lowZeroSeedP1J0I3K1Point,lowZeroSeedP1J0I3K4Point]
  · convert lowZeroCoefficientsP1J0I3K5_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP1J0I3Coefficient,lowZeroSeedP1J0I3K1Point,lowZeroSeedP1J0I3K5Point]

def lowZeroPanelP1J0I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/16) lowZeroPanelP1J0I3Coefficient

theorem lowZeroPanelP1J0I3Value_eq : lowZeroPanelP1J0I3Value=(-2878012758967274649240533993175625204729311563977560859624550433062099432797525605474252394553090384893768850501839201905779399879102965046287399318651891385837364599825466853628591839151857:ℚ)/1689263502853853276647019390918250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP1J0I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP1J0I3K1Point (theta48PanelCenter 0 3)
      (theta48PanelHalfWidth 0) 80-(lowZeroPanelP1J0I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP1J0I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP1J0I3K1Point (theta48PanelCenter 0 3)
    ((1:ℚ)/16) lowZeroPanelP1J0I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP1J0I3Value,theta48PanelHalfWidth]

end ReciprocalXi
