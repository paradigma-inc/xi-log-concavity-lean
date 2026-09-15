import ProofWorkspace.Final.SourceBlock3008Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3040DataFull
import ProofWorkspace.Final.EtaBlock3040Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3040XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3040+k) (sourceBlock3040PiPairs.getD k (0,0))
    (sourceEtaBatch3040Lower k, sourceEtaBatch3040Upper k)
    (sourceBlock3040TwoPairs.getD k (0,0))

theorem sourceBlock3040Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3040XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3040+k):ℂ)).re ∧
      (xi (xiGridArgument (3040+k):ℂ)).re ≤ ((sourceBlock3040XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3040+k) _ _ _
    (sourceBlock3040PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3040_actual_enclosure k hk)
    (sourceBlock3040TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3040Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3040XiPair k).1 := by
  decide +kernel

theorem sourceBlock3040Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3040Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3040XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3040XiPair k)).2 ≤
      sourceBlock3040Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3040_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3040+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3040+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3040Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3040+k) (sourceBlock3040XiPair k) _
    (sourceBlock3040Xi_enclosure k hk) (sourceBlock3040Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3040Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3072_bound (k : ℕ) (hk : k < 3072) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3040
  · exact sourceRoundedMidpoint_first3040_bound k h
  · have hsum : 3040+(k-3040) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3040_bound (k-3040) (by omega)

end ReciprocalXi
