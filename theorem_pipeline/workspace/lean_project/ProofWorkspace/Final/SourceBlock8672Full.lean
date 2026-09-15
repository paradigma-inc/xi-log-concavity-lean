import ProofWorkspace.Final.SourceBlock8640Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8672DataFull
import ProofWorkspace.Final.EtaBlock8672Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8672XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8672+k) (sourceBlock8672PiPairs.getD k (0,0))
    (sourceEtaBatch8672Lower k, sourceEtaBatch8672Upper k)
    (sourceBlock8672TwoPairs.getD k (0,0))

theorem sourceBlock8672Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8672XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8672+k):ℂ)).re ∧
      (xi (xiGridArgument (8672+k):ℂ)).re ≤ ((sourceBlock8672XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8672+k) _ _ _
    (sourceBlock8672PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8672_actual_enclosure k hk)
    (sourceBlock8672TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8672Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8672XiPair k).1 := by
  decide +kernel

theorem sourceBlock8672Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8672Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8672XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8672XiPair k)).2 ≤
      sourceBlock8672Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8672_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8672+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8672+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8672Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8672+k) (sourceBlock8672XiPair k) _
    (sourceBlock8672Xi_enclosure k hk) (sourceBlock8672Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8672Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8704_bound (k : ℕ) (hk : k < 8704) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8672
  · exact sourceRoundedMidpoint_first8672_bound k h
  · have hsum : 8672+(k-8672) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8672_bound (k-8672) (by omega)

end ReciprocalXi
