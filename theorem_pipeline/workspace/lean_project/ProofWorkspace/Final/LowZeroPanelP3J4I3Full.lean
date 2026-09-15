import ProofWorkspace.Final.XiLowZeroStoredQuadratureFull
import ProofWorkspace.Final.XiLowZeroFarAtomsFull
import ProofWorkspace.Final.LowZeroCoefficientsP3J4I3K1Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def lowZeroPanelP3J4I3Coefficient (k n : ℕ) : ℚ × ℚ :=
  match k with
  | 0 => lowZeroCoefficientsP3J4I3K1State n
  | 1 => (0,0)
  | 2 => (0,0)
  | 3 => (0,0)
  | 4 => (0,0)
  | _ => (0,0)

theorem lowZeroPanelP3J4I3_coefficients_error (k n : ℕ) (hk : k<5) (hn : n<80) :
    ‖ratComplexValue (lowZeroPanelP3J4I3Coefficient k n)-
      scaledPowerExpCoefficient (complexThetaExponent lowZeroSeedP3J4I3K1Point)
        (theta48PanelCenter 4 3:ℂ) (Real.pi*((k:ℝ)+1)^2)
        (theta48PanelHalfWidth 4) n‖≤1/(10:ℝ)^50 := by
  interval_cases k
  · convert lowZeroCoefficientsP3J4I3K1_actual_coefficient_error n hn using 1 <;>
      norm_num [lowZeroPanelP3J4I3Coefficient,lowZeroSeedP3J4I3K1Point,lowZeroSeedP3J4I3K1Point]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I3K1Point
        (theta48PanelCenter 4 3) (theta48PanelHalfWidth 4) 2 n
        (by norm_num [lowZeroSeedP3J4I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I3K1Point
        (theta48PanelCenter 4 3) (theta48PanelHalfWidth 4) 3 n
        (by norm_num [lowZeroSeedP3J4I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I3K1Point
        (theta48PanelCenter 4 3) (theta48PanelHalfWidth 4) 4 n
        (by norm_num [lowZeroSeedP3J4I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I3Coefficient]
  · have he := lowZeroFarAtom_zeroCoefficient_error lowZeroSeedP3J4I3K1Point
        (theta48PanelCenter 4 3) (theta48PanelHalfWidth 4) 5 n
        (by norm_num [lowZeroSeedP3J4I3K1Point])
        (by norm_num [theta48PanelCenter])
        (by norm_num [theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter,theta48PanelHalfWidth])
        (by norm_num [theta48PanelCenter])
    convert he using 1 <;> norm_num [lowZeroPanelP3J4I3Coefficient]

def lowZeroPanelP3J4I3Value : ℚ := ratLowZeroApproxPanelValue ((1:ℚ)/1) lowZeroPanelP3J4I3Coefficient

theorem lowZeroPanelP3J4I3Value_eq : lowZeroPanelP3J4I3Value=(3670501680491658012919738504435926064222222935190577066096111648184058929198008029611820984696109191819845873110748013742110904231625905723039667784167662886409:ℚ)/180992518162912851069323506169812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel

theorem lowZeroPanelP3J4I3_panel_error :
    |lowZeroThetaTaylorPanelValue lowZeroSeedP3J4I3K1Point (theta48PanelCenter 4 3)
      (theta48PanelHalfWidth 4) 80-(lowZeroPanelP3J4I3Value:ℝ)|≤1600/(10:ℝ)^50 := by
  have hw := lowZeroPanelP3J4I3_coefficients_error
  have he := ratLowZeroPanel_error lowZeroSeedP3J4I3K1Point (theta48PanelCenter 4 3)
    ((1:ℚ)/1) lowZeroPanelP3J4I3Coefficient (by norm_num [theta48PanelCenter])
    (by decide +kernel) (by decide +kernel) (by
      intro k hk n hn
      convert hw k n hk hn using 1 <;> norm_num [theta48PanelHalfWidth])
  convert he using 1 <;> norm_num [lowZeroPanelP3J4I3Value,theta48PanelHalfWidth]

end ReciprocalXi
