import ProofWorkspace.Final.SourceBlock6016Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6048DataFull
import ProofWorkspace.Final.EtaBlock6048Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6048XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6048+k) (sourceBlock6048PiPairs.getD k (0,0))
    (sourceEtaBatch6048Lower k, sourceEtaBatch6048Upper k)
    (sourceBlock6048TwoPairs.getD k (0,0))

theorem sourceBlock6048Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6048XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6048+k):ℂ)).re ∧
      (xi (xiGridArgument (6048+k):ℂ)).re ≤ ((sourceBlock6048XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6048+k) _ _ _
    (sourceBlock6048PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6048_actual_enclosure k hk)
    (sourceBlock6048TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6048Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6048XiPair k).1 := by
  decide +kernel

theorem sourceBlock6048Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6048Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6048XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6048XiPair k)).2 ≤
      sourceBlock6048Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6048_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6048+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6048+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6048Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6048+k) (sourceBlock6048XiPair k) _
    (sourceBlock6048Xi_enclosure k hk) (sourceBlock6048Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6048Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6080_bound (k : ℕ) (hk : k < 6080) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6048
  · exact sourceRoundedMidpoint_first6048_bound k h
  · have hsum : 6048+(k-6048) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6048_bound (k-6048) (by omega)

end ReciprocalXi
