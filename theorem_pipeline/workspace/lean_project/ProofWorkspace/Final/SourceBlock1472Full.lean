import ProofWorkspace.Final.SourceBlock1440Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1472DataFull
import ProofWorkspace.Final.EtaBlock1472Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1472XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1472+k) (sourceBlock1472PiPairs.getD k (0,0))
    (sourceEtaBatch1472Lower k, sourceEtaBatch1472Upper k)
    (sourceBlock1472TwoPairs.getD k (0,0))

theorem sourceBlock1472Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1472XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1472+k):ℂ)).re ∧
      (xi (xiGridArgument (1472+k):ℂ)).re ≤ ((sourceBlock1472XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1472+k) _ _ _
    (sourceBlock1472PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1472_actual_enclosure k hk)
    (sourceBlock1472TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1472Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1472XiPair k).1 := by
  decide +kernel

theorem sourceBlock1472Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1472Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1472XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1472XiPair k)).2 ≤
      sourceBlock1472Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1472_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1472+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1472+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1472Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1472+k) (sourceBlock1472XiPair k) _
    (sourceBlock1472Xi_enclosure k hk) (sourceBlock1472Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1472Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1504_bound (k : ℕ) (hk : k < 1504) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1472
  · exact sourceRoundedMidpoint_first1472_bound k h
  · have hsum : 1472+(k-1472) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1472_bound (k-1472) (by omega)

end ReciprocalXi
