import ProofWorkspace.Final.SourceBlock3488Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3520DataFull
import ProofWorkspace.Final.EtaBlock3520Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3520XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3520+k) (sourceBlock3520PiPairs.getD k (0,0))
    (sourceEtaBatch3520Lower k, sourceEtaBatch3520Upper k)
    (sourceBlock3520TwoPairs.getD k (0,0))

theorem sourceBlock3520Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3520XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3520+k):ℂ)).re ∧
      (xi (xiGridArgument (3520+k):ℂ)).re ≤ ((sourceBlock3520XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3520+k) _ _ _
    (sourceBlock3520PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3520_actual_enclosure k hk)
    (sourceBlock3520TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3520Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3520XiPair k).1 := by
  decide +kernel

theorem sourceBlock3520Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3520Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3520XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3520XiPair k)).2 ≤
      sourceBlock3520Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3520_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3520+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3520+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3520Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3520+k) (sourceBlock3520XiPair k) _
    (sourceBlock3520Xi_enclosure k hk) (sourceBlock3520Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3520Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3552_bound (k : ℕ) (hk : k < 3552) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3520
  · exact sourceRoundedMidpoint_first3520_bound k h
  · have hsum : 3520+(k-3520) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3520_bound (k-3520) (by omega)

end ReciprocalXi
