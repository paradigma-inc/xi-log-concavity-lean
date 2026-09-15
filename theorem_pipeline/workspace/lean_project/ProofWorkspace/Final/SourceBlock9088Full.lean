import ProofWorkspace.Final.SourceBlock9056Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9088DataFull
import ProofWorkspace.Final.EtaBlock9088Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9088XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9088+k) (sourceBlock9088PiPairs.getD k (0,0))
    (sourceEtaBatch9088Lower k, sourceEtaBatch9088Upper k)
    (sourceBlock9088TwoPairs.getD k (0,0))

theorem sourceBlock9088Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9088XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9088+k):ℂ)).re ∧
      (xi (xiGridArgument (9088+k):ℂ)).re ≤ ((sourceBlock9088XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9088+k) _ _ _
    (sourceBlock9088PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9088_actual_enclosure k hk)
    (sourceBlock9088TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9088Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9088XiPair k).1 := by
  decide +kernel

theorem sourceBlock9088Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9088Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9088XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9088XiPair k)).2 ≤
      sourceBlock9088Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9088_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9088+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9088+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9088Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9088+k) (sourceBlock9088XiPair k) _
    (sourceBlock9088Xi_enclosure k hk) (sourceBlock9088Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9088Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9120_bound (k : ℕ) (hk : k < 9120) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9088
  · exact sourceRoundedMidpoint_first9088_bound k h
  · have hsum : 9088+(k-9088) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9088_bound (k-9088) (by omega)

end ReciprocalXi
