import ProofWorkspace.Final.SourceBlock1056Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1088DataFull
import ProofWorkspace.Final.EtaBlock1088Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1088XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1088+k) (sourceBlock1088PiPairs.getD k (0,0))
    (sourceEtaBatch1088Lower k, sourceEtaBatch1088Upper k)
    (sourceBlock1088TwoPairs.getD k (0,0))

theorem sourceBlock1088Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1088XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1088+k):ℂ)).re ∧
      (xi (xiGridArgument (1088+k):ℂ)).re ≤ ((sourceBlock1088XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1088+k) _ _ _
    (sourceBlock1088PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1088_actual_enclosure k hk)
    (sourceBlock1088TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1088Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1088XiPair k).1 := by
  decide +kernel

theorem sourceBlock1088Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1088Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1088XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1088XiPair k)).2 ≤
      sourceBlock1088Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1088_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1088+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1088+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1088Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1088+k) (sourceBlock1088XiPair k) _
    (sourceBlock1088Xi_enclosure k hk) (sourceBlock1088Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1088Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1120_bound (k : ℕ) (hk : k < 1120) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1088
  · exact sourceRoundedMidpoint_first1088_bound k h
  · have hsum : 1088+(k-1088) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1088_bound (k-1088) (by omega)

end ReciprocalXi
