import ProofWorkspace.Final.SourceBlock1376Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1408DataFull
import ProofWorkspace.Final.EtaBlock1408Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1408XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1408+k) (sourceBlock1408PiPairs.getD k (0,0))
    (sourceEtaBatch1408Lower k, sourceEtaBatch1408Upper k)
    (sourceBlock1408TwoPairs.getD k (0,0))

theorem sourceBlock1408Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1408XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1408+k):ℂ)).re ∧
      (xi (xiGridArgument (1408+k):ℂ)).re ≤ ((sourceBlock1408XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1408+k) _ _ _
    (sourceBlock1408PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1408_actual_enclosure k hk)
    (sourceBlock1408TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1408Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1408XiPair k).1 := by
  decide +kernel

theorem sourceBlock1408Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1408Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1408XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1408XiPair k)).2 ≤
      sourceBlock1408Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1408_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1408+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1408+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1408Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1408+k) (sourceBlock1408XiPair k) _
    (sourceBlock1408Xi_enclosure k hk) (sourceBlock1408Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1408Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1440_bound (k : ℕ) (hk : k < 1440) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1408
  · exact sourceRoundedMidpoint_first1408_bound k h
  · have hsum : 1408+(k-1408) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1408_bound (k-1408) (by omega)

end ReciprocalXi
