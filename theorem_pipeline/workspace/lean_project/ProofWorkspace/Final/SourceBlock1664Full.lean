import ProofWorkspace.Final.SourceBlock1632Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1664DataFull
import ProofWorkspace.Final.EtaBlock1664Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1664XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1664+k) (sourceBlock1664PiPairs.getD k (0,0))
    (sourceEtaBatch1664Lower k, sourceEtaBatch1664Upper k)
    (sourceBlock1664TwoPairs.getD k (0,0))

theorem sourceBlock1664Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1664XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1664+k):ℂ)).re ∧
      (xi (xiGridArgument (1664+k):ℂ)).re ≤ ((sourceBlock1664XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1664+k) _ _ _
    (sourceBlock1664PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1664_actual_enclosure k hk)
    (sourceBlock1664TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1664Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1664XiPair k).1 := by
  decide +kernel

theorem sourceBlock1664Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1664Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1664XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1664XiPair k)).2 ≤
      sourceBlock1664Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1664_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1664+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1664+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1664Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1664+k) (sourceBlock1664XiPair k) _
    (sourceBlock1664Xi_enclosure k hk) (sourceBlock1664Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1664Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1696_bound (k : ℕ) (hk : k < 1696) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1664
  · exact sourceRoundedMidpoint_first1664_bound k h
  · have hsum : 1664+(k-1664) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1664_bound (k-1664) (by omega)

end ReciprocalXi
