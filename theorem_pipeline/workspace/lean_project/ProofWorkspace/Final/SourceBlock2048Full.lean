import ProofWorkspace.Final.SourceBlock2016Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2048DataFull
import ProofWorkspace.Final.EtaBlock2048Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2048XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2048+k) (sourceBlock2048PiPairs.getD k (0,0))
    (sourceEtaBatch2048Lower k, sourceEtaBatch2048Upper k)
    (sourceBlock2048TwoPairs.getD k (0,0))

theorem sourceBlock2048Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2048XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2048+k):ℂ)).re ∧
      (xi (xiGridArgument (2048+k):ℂ)).re ≤ ((sourceBlock2048XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2048+k) _ _ _
    (sourceBlock2048PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2048_actual_enclosure k hk)
    (sourceBlock2048TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2048Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2048XiPair k).1 := by
  decide +kernel

theorem sourceBlock2048Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2048Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2048XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2048XiPair k)).2 ≤
      sourceBlock2048Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2048_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2048+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2048+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2048Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2048+k) (sourceBlock2048XiPair k) _
    (sourceBlock2048Xi_enclosure k hk) (sourceBlock2048Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2048Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2080_bound (k : ℕ) (hk : k < 2080) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2048
  · exact sourceRoundedMidpoint_first2048_bound k h
  · have hsum : 2048+(k-2048) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2048_bound (k-2048) (by omega)

end ReciprocalXi
