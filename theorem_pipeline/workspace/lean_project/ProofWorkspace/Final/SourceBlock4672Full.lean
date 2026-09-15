import ProofWorkspace.Final.SourceBlock4640Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4672DataFull
import ProofWorkspace.Final.EtaBlock4672Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4672XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4672+k) (sourceBlock4672PiPairs.getD k (0,0))
    (sourceEtaBatch4672Lower k, sourceEtaBatch4672Upper k)
    (sourceBlock4672TwoPairs.getD k (0,0))

theorem sourceBlock4672Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4672XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4672+k):ℂ)).re ∧
      (xi (xiGridArgument (4672+k):ℂ)).re ≤ ((sourceBlock4672XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4672+k) _ _ _
    (sourceBlock4672PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4672_actual_enclosure k hk)
    (sourceBlock4672TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4672Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4672XiPair k).1 := by
  decide +kernel

theorem sourceBlock4672Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4672Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4672XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4672XiPair k)).2 ≤
      sourceBlock4672Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4672_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4672+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4672+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4672Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4672+k) (sourceBlock4672XiPair k) _
    (sourceBlock4672Xi_enclosure k hk) (sourceBlock4672Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4672Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4704_bound (k : ℕ) (hk : k < 4704) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4672
  · exact sourceRoundedMidpoint_first4672_bound k h
  · have hsum : 4672+(k-4672) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4672_bound (k-4672) (by omega)

end ReciprocalXi
