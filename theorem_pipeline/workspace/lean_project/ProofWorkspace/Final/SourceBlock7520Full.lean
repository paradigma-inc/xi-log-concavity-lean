import ProofWorkspace.Final.SourceBlock7488Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7520DataFull
import ProofWorkspace.Final.EtaBlock7520Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7520XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7520+k) (sourceBlock7520PiPairs.getD k (0,0))
    (sourceEtaBatch7520Lower k, sourceEtaBatch7520Upper k)
    (sourceBlock7520TwoPairs.getD k (0,0))

theorem sourceBlock7520Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7520XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7520+k):ℂ)).re ∧
      (xi (xiGridArgument (7520+k):ℂ)).re ≤ ((sourceBlock7520XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7520+k) _ _ _
    (sourceBlock7520PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7520_actual_enclosure k hk)
    (sourceBlock7520TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7520Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7520XiPair k).1 := by
  decide +kernel

theorem sourceBlock7520Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7520Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7520XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7520XiPair k)).2 ≤
      sourceBlock7520Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7520_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7520+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7520+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7520Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7520+k) (sourceBlock7520XiPair k) _
    (sourceBlock7520Xi_enclosure k hk) (sourceBlock7520Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7520Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7552_bound (k : ℕ) (hk : k < 7552) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7520
  · exact sourceRoundedMidpoint_first7520_bound k h
  · have hsum : 7520+(k-7520) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7520_bound (k-7520) (by omega)

end ReciprocalXi
