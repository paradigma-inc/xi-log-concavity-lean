import ProofWorkspace.Final.SourceBlock6240Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6272DataFull
import ProofWorkspace.Final.EtaBlock6272Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6272XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6272+k) (sourceBlock6272PiPairs.getD k (0,0))
    (sourceEtaBatch6272Lower k, sourceEtaBatch6272Upper k)
    (sourceBlock6272TwoPairs.getD k (0,0))

theorem sourceBlock6272Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6272XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6272+k):ℂ)).re ∧
      (xi (xiGridArgument (6272+k):ℂ)).re ≤ ((sourceBlock6272XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6272+k) _ _ _
    (sourceBlock6272PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6272_actual_enclosure k hk)
    (sourceBlock6272TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6272Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6272XiPair k).1 := by
  decide +kernel

theorem sourceBlock6272Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6272Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6272XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6272XiPair k)).2 ≤
      sourceBlock6272Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6272_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6272+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6272+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6272Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6272+k) (sourceBlock6272XiPair k) _
    (sourceBlock6272Xi_enclosure k hk) (sourceBlock6272Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6272Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6304_bound (k : ℕ) (hk : k < 6304) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6272
  · exact sourceRoundedMidpoint_first6272_bound k h
  · have hsum : 6272+(k-6272) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6272_bound (k-6272) (by omega)

end ReciprocalXi
