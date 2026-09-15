import ProofWorkspace.Final.SourceBlock5376Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5408DataFull
import ProofWorkspace.Final.EtaBlock5408Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5408XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5408+k) (sourceBlock5408PiPairs.getD k (0,0))
    (sourceEtaBatch5408Lower k, sourceEtaBatch5408Upper k)
    (sourceBlock5408TwoPairs.getD k (0,0))

theorem sourceBlock5408Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5408XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5408+k):ℂ)).re ∧
      (xi (xiGridArgument (5408+k):ℂ)).re ≤ ((sourceBlock5408XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5408+k) _ _ _
    (sourceBlock5408PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5408_actual_enclosure k hk)
    (sourceBlock5408TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5408Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5408XiPair k).1 := by
  decide +kernel

theorem sourceBlock5408Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5408Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5408XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5408XiPair k)).2 ≤
      sourceBlock5408Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5408_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5408+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5408+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5408Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5408+k) (sourceBlock5408XiPair k) _
    (sourceBlock5408Xi_enclosure k hk) (sourceBlock5408Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5408Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5440_bound (k : ℕ) (hk : k < 5440) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5408
  · exact sourceRoundedMidpoint_first5408_bound k h
  · have hsum : 5408+(k-5408) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5408_bound (k-5408) (by omega)

end ReciprocalXi
