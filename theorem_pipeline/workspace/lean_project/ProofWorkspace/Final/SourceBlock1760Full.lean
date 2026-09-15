import ProofWorkspace.Final.SourceBlock1728Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1760DataFull
import ProofWorkspace.Final.EtaBlock1760Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1760XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1760+k) (sourceBlock1760PiPairs.getD k (0,0))
    (sourceEtaBatch1760Lower k, sourceEtaBatch1760Upper k)
    (sourceBlock1760TwoPairs.getD k (0,0))

theorem sourceBlock1760Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1760XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1760+k):ℂ)).re ∧
      (xi (xiGridArgument (1760+k):ℂ)).re ≤ ((sourceBlock1760XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1760+k) _ _ _
    (sourceBlock1760PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1760_actual_enclosure k hk)
    (sourceBlock1760TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1760Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1760XiPair k).1 := by
  decide +kernel

theorem sourceBlock1760Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1760Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1760XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1760XiPair k)).2 ≤
      sourceBlock1760Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1760_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1760+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1760+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1760Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1760+k) (sourceBlock1760XiPair k) _
    (sourceBlock1760Xi_enclosure k hk) (sourceBlock1760Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1760Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1792_bound (k : ℕ) (hk : k < 1792) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1760
  · exact sourceRoundedMidpoint_first1760_bound k h
  · have hsum : 1760+(k-1760) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1760_bound (k-1760) (by omega)

end ReciprocalXi
