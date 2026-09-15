import ProofWorkspace.Final.SourceBlock2240Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2272DataFull
import ProofWorkspace.Final.EtaBlock2272Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2272XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2272+k) (sourceBlock2272PiPairs.getD k (0,0))
    (sourceEtaBatch2272Lower k, sourceEtaBatch2272Upper k)
    (sourceBlock2272TwoPairs.getD k (0,0))

theorem sourceBlock2272Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2272XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2272+k):ℂ)).re ∧
      (xi (xiGridArgument (2272+k):ℂ)).re ≤ ((sourceBlock2272XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2272+k) _ _ _
    (sourceBlock2272PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2272_actual_enclosure k hk)
    (sourceBlock2272TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2272Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2272XiPair k).1 := by
  decide +kernel

theorem sourceBlock2272Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2272Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2272XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2272XiPair k)).2 ≤
      sourceBlock2272Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2272_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2272+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2272+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2272Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2272+k) (sourceBlock2272XiPair k) _
    (sourceBlock2272Xi_enclosure k hk) (sourceBlock2272Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2272Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2304_bound (k : ℕ) (hk : k < 2304) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2272
  · exact sourceRoundedMidpoint_first2272_bound k h
  · have hsum : 2272+(k-2272) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2272_bound (k-2272) (by omega)

end ReciprocalXi
