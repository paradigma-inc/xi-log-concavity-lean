import ProofWorkspace.Final.SourceBlock5984Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6016DataFull
import ProofWorkspace.Final.EtaBlock6016Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6016XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6016+k) (sourceBlock6016PiPairs.getD k (0,0))
    (sourceEtaBatch6016Lower k, sourceEtaBatch6016Upper k)
    (sourceBlock6016TwoPairs.getD k (0,0))

theorem sourceBlock6016Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6016XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6016+k):ℂ)).re ∧
      (xi (xiGridArgument (6016+k):ℂ)).re ≤ ((sourceBlock6016XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6016+k) _ _ _
    (sourceBlock6016PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6016_actual_enclosure k hk)
    (sourceBlock6016TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6016Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6016XiPair k).1 := by
  decide +kernel

theorem sourceBlock6016Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6016Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6016XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6016XiPair k)).2 ≤
      sourceBlock6016Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6016_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6016+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6016+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6016Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6016+k) (sourceBlock6016XiPair k) _
    (sourceBlock6016Xi_enclosure k hk) (sourceBlock6016Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6016Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6048_bound (k : ℕ) (hk : k < 6048) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6016
  · exact sourceRoundedMidpoint_first6016_bound k h
  · have hsum : 6016+(k-6016) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6016_bound (k-6016) (by omega)

end ReciprocalXi
