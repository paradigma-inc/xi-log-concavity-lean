import ProofWorkspace.Final.SourceBlock2208Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2240DataFull
import ProofWorkspace.Final.EtaBlock2240Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2240XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2240+k) (sourceBlock2240PiPairs.getD k (0,0))
    (sourceEtaBatch2240Lower k, sourceEtaBatch2240Upper k)
    (sourceBlock2240TwoPairs.getD k (0,0))

theorem sourceBlock2240Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2240XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2240+k):ℂ)).re ∧
      (xi (xiGridArgument (2240+k):ℂ)).re ≤ ((sourceBlock2240XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2240+k) _ _ _
    (sourceBlock2240PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2240_actual_enclosure k hk)
    (sourceBlock2240TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2240Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2240XiPair k).1 := by
  decide +kernel

theorem sourceBlock2240Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2240Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2240XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2240XiPair k)).2 ≤
      sourceBlock2240Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2240_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2240+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2240+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2240Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2240+k) (sourceBlock2240XiPair k) _
    (sourceBlock2240Xi_enclosure k hk) (sourceBlock2240Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2240Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2272_bound (k : ℕ) (hk : k < 2272) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2240
  · exact sourceRoundedMidpoint_first2240_bound k h
  · have hsum : 2240+(k-2240) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2240_bound (k-2240) (by omega)

end ReciprocalXi
