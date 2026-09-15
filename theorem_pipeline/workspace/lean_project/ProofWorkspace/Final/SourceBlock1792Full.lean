import ProofWorkspace.Final.SourceBlock1760Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1792DataFull
import ProofWorkspace.Final.EtaBlock1792Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1792XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1792+k) (sourceBlock1792PiPairs.getD k (0,0))
    (sourceEtaBatch1792Lower k, sourceEtaBatch1792Upper k)
    (sourceBlock1792TwoPairs.getD k (0,0))

theorem sourceBlock1792Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1792XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1792+k):ℂ)).re ∧
      (xi (xiGridArgument (1792+k):ℂ)).re ≤ ((sourceBlock1792XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1792+k) _ _ _
    (sourceBlock1792PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1792_actual_enclosure k hk)
    (sourceBlock1792TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1792Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1792XiPair k).1 := by
  decide +kernel

theorem sourceBlock1792Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1792Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1792XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1792XiPair k)).2 ≤
      sourceBlock1792Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1792_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1792+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1792+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1792Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1792+k) (sourceBlock1792XiPair k) _
    (sourceBlock1792Xi_enclosure k hk) (sourceBlock1792Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1792Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1824_bound (k : ℕ) (hk : k < 1824) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1792
  · exact sourceRoundedMidpoint_first1792_bound k h
  · have hsum : 1792+(k-1792) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1792_bound (k-1792) (by omega)

end ReciprocalXi
