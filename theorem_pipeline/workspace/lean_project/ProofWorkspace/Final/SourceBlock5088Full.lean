import ProofWorkspace.Final.SourceBlock5056Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5088DataFull
import ProofWorkspace.Final.EtaBlock5088Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5088XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5088+k) (sourceBlock5088PiPairs.getD k (0,0))
    (sourceEtaBatch5088Lower k, sourceEtaBatch5088Upper k)
    (sourceBlock5088TwoPairs.getD k (0,0))

theorem sourceBlock5088Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5088XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5088+k):ℂ)).re ∧
      (xi (xiGridArgument (5088+k):ℂ)).re ≤ ((sourceBlock5088XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5088+k) _ _ _
    (sourceBlock5088PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5088_actual_enclosure k hk)
    (sourceBlock5088TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5088Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5088XiPair k).1 := by
  decide +kernel

theorem sourceBlock5088Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5088Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5088XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5088XiPair k)).2 ≤
      sourceBlock5088Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5088_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5088+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5088+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5088Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5088+k) (sourceBlock5088XiPair k) _
    (sourceBlock5088Xi_enclosure k hk) (sourceBlock5088Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5088Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5120_bound (k : ℕ) (hk : k < 5120) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5088
  · exact sourceRoundedMidpoint_first5088_bound k h
  · have hsum : 5088+(k-5088) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5088_bound (k-5088) (by omega)

end ReciprocalXi
