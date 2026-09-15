import ProofWorkspace.Final.SourceBlock10368Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10400DataFull
import ProofWorkspace.Final.EtaBlock10400Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10400XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10400+k) (sourceBlock10400PiPairs.getD k (0,0))
    (sourceEtaBatch10400Lower k, sourceEtaBatch10400Upper k)
    (sourceBlock10400TwoPairs.getD k (0,0))

theorem sourceBlock10400Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10400XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10400+k):ℂ)).re ∧
      (xi (xiGridArgument (10400+k):ℂ)).re ≤ ((sourceBlock10400XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10400+k) _ _ _
    (sourceBlock10400PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10400_actual_enclosure k hk)
    (sourceBlock10400TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10400Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10400XiPair k).1 := by
  decide +kernel

theorem sourceBlock10400Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10400Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10400XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10400XiPair k)).2 ≤
      sourceBlock10400Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10400_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10400+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10400+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10400Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10400+k) (sourceBlock10400XiPair k) _
    (sourceBlock10400Xi_enclosure k hk) (sourceBlock10400Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10400Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10432_bound (k : ℕ) (hk : k < 10432) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10400
  · exact sourceRoundedMidpoint_first10400_bound k h
  · have hsum : 10400+(k-10400) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10400_bound (k-10400) (by omega)

end ReciprocalXi
