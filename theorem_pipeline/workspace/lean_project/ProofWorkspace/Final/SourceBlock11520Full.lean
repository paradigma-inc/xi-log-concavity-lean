import ProofWorkspace.Final.SourceBlock11488Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11520DataFull
import ProofWorkspace.Final.EtaBlock11520Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11520XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11520+k) (sourceBlock11520PiPairs.getD k (0,0))
    (sourceEtaBatch11520Lower k, sourceEtaBatch11520Upper k)
    (sourceBlock11520TwoPairs.getD k (0,0))

theorem sourceBlock11520Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11520XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11520+k):ℂ)).re ∧
      (xi (xiGridArgument (11520+k):ℂ)).re ≤ ((sourceBlock11520XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11520+k) _ _ _
    (sourceBlock11520PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11520_actual_enclosure k hk)
    (sourceBlock11520TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11520Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11520XiPair k).1 := by
  decide +kernel

theorem sourceBlock11520Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11520Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11520XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11520XiPair k)).2 ≤
      sourceBlock11520Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11520_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11520+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11520+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11520Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11520+k) (sourceBlock11520XiPair k) _
    (sourceBlock11520Xi_enclosure k hk) (sourceBlock11520Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11520Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11552_bound (k : ℕ) (hk : k < 11552) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11520
  · exact sourceRoundedMidpoint_first11520_bound k h
  · have hsum : 11520+(k-11520) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11520_bound (k-11520) (by omega)

end ReciprocalXi
