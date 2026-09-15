import ProofWorkspace.Final.SourceBlock6560Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6592DataFull
import ProofWorkspace.Final.EtaBlock6592Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6592XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6592+k) (sourceBlock6592PiPairs.getD k (0,0))
    (sourceEtaBatch6592Lower k, sourceEtaBatch6592Upper k)
    (sourceBlock6592TwoPairs.getD k (0,0))

theorem sourceBlock6592Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6592XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6592+k):ℂ)).re ∧
      (xi (xiGridArgument (6592+k):ℂ)).re ≤ ((sourceBlock6592XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6592+k) _ _ _
    (sourceBlock6592PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6592_actual_enclosure k hk)
    (sourceBlock6592TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6592Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6592XiPair k).1 := by
  decide +kernel

theorem sourceBlock6592Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6592Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6592XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6592XiPair k)).2 ≤
      sourceBlock6592Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6592_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6592+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6592+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6592Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6592+k) (sourceBlock6592XiPair k) _
    (sourceBlock6592Xi_enclosure k hk) (sourceBlock6592Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6592Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6624_bound (k : ℕ) (hk : k < 6624) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6592
  · exact sourceRoundedMidpoint_first6592_bound k h
  · have hsum : 6592+(k-6592) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6592_bound (k-6592) (by omega)

end ReciprocalXi
