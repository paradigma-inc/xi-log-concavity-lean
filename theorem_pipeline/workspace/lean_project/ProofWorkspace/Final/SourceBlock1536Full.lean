import ProofWorkspace.Final.SourceBlock1504Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1536DataFull
import ProofWorkspace.Final.EtaBlock1536Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1536XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1536+k) (sourceBlock1536PiPairs.getD k (0,0))
    (sourceEtaBatch1536Lower k, sourceEtaBatch1536Upper k)
    (sourceBlock1536TwoPairs.getD k (0,0))

theorem sourceBlock1536Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1536XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1536+k):ℂ)).re ∧
      (xi (xiGridArgument (1536+k):ℂ)).re ≤ ((sourceBlock1536XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1536+k) _ _ _
    (sourceBlock1536PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1536_actual_enclosure k hk)
    (sourceBlock1536TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1536Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1536XiPair k).1 := by
  decide +kernel

theorem sourceBlock1536Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1536Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1536XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1536XiPair k)).2 ≤
      sourceBlock1536Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1536_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1536+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1536+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1536Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1536+k) (sourceBlock1536XiPair k) _
    (sourceBlock1536Xi_enclosure k hk) (sourceBlock1536Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1536Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1568_bound (k : ℕ) (hk : k < 1568) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1536
  · exact sourceRoundedMidpoint_first1536_bound k h
  · have hsum : 1536+(k-1536) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1536_bound (k-1536) (by omega)

end ReciprocalXi
