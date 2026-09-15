import ProofWorkspace.Final.SourceBlock2560Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2592DataFull
import ProofWorkspace.Final.EtaBlock2592Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2592XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2592+k) (sourceBlock2592PiPairs.getD k (0,0))
    (sourceEtaBatch2592Lower k, sourceEtaBatch2592Upper k)
    (sourceBlock2592TwoPairs.getD k (0,0))

theorem sourceBlock2592Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2592XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2592+k):ℂ)).re ∧
      (xi (xiGridArgument (2592+k):ℂ)).re ≤ ((sourceBlock2592XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2592+k) _ _ _
    (sourceBlock2592PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2592_actual_enclosure k hk)
    (sourceBlock2592TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2592Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2592XiPair k).1 := by
  decide +kernel

theorem sourceBlock2592Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2592Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2592XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2592XiPair k)).2 ≤
      sourceBlock2592Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2592_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2592+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2592+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2592Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2592+k) (sourceBlock2592XiPair k) _
    (sourceBlock2592Xi_enclosure k hk) (sourceBlock2592Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2592Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2624_bound (k : ℕ) (hk : k < 2624) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2592
  · exact sourceRoundedMidpoint_first2592_bound k h
  · have hsum : 2592+(k-2592) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2592_bound (k-2592) (by omega)

end ReciprocalXi
