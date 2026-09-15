import ProofWorkspace.Final.SourceBlock640Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock672DataFull
import ProofWorkspace.Final.EtaBlock672Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock672XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (672+k) (sourceBlock672PiPairs.getD k (0,0))
    (sourceEtaBatch672Lower k, sourceEtaBatch672Upper k)
    (sourceBlock672TwoPairs.getD k (0,0))

theorem sourceBlock672Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock672XiPair k).1:ℝ) ≤ (xi (xiGridArgument (672+k):ℂ)).re ∧
      (xi (xiGridArgument (672+k):ℂ)).re ≤ ((sourceBlock672XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (672+k) _ _ _
    (sourceBlock672PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch672_actual_enclosure k hk)
    (sourceBlock672TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock672Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock672XiPair k).1 := by
  decide +kernel

theorem sourceBlock672Reciprocal_check : ∀ k : Fin 32,
    sourceBlock672Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock672XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock672XiPair k)).2 ≤
      sourceBlock672Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block672_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((672+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (672+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock672Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (672+k) (sourceBlock672XiPair k) _
    (sourceBlock672Xi_enclosure k hk) (sourceBlock672Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock672Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first704_bound (k : ℕ) (hk : k < 704) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 672
  · exact sourceRoundedMidpoint_first672_bound k h
  · have hsum : 672+(k-672) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block672_bound (k-672) (by omega)

end ReciprocalXi
