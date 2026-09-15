import ProofWorkspace.Final.SourceBlock1696Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1728DataFull
import ProofWorkspace.Final.EtaBlock1728Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1728XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1728+k) (sourceBlock1728PiPairs.getD k (0,0))
    (sourceEtaBatch1728Lower k, sourceEtaBatch1728Upper k)
    (sourceBlock1728TwoPairs.getD k (0,0))

theorem sourceBlock1728Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1728XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1728+k):ℂ)).re ∧
      (xi (xiGridArgument (1728+k):ℂ)).re ≤ ((sourceBlock1728XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1728+k) _ _ _
    (sourceBlock1728PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1728_actual_enclosure k hk)
    (sourceBlock1728TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1728Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1728XiPair k).1 := by
  decide +kernel

theorem sourceBlock1728Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1728Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1728XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1728XiPair k)).2 ≤
      sourceBlock1728Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1728_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1728+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1728+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1728Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1728+k) (sourceBlock1728XiPair k) _
    (sourceBlock1728Xi_enclosure k hk) (sourceBlock1728Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1728Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1760_bound (k : ℕ) (hk : k < 1760) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1728
  · exact sourceRoundedMidpoint_first1728_bound k h
  · have hsum : 1728+(k-1728) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1728_bound (k-1728) (by omega)

end ReciprocalXi
