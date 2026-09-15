import ProofWorkspace.Final.SourceBlock5440Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5472DataFull
import ProofWorkspace.Final.EtaBlock5472Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5472XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5472+k) (sourceBlock5472PiPairs.getD k (0,0))
    (sourceEtaBatch5472Lower k, sourceEtaBatch5472Upper k)
    (sourceBlock5472TwoPairs.getD k (0,0))

theorem sourceBlock5472Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5472XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5472+k):ℂ)).re ∧
      (xi (xiGridArgument (5472+k):ℂ)).re ≤ ((sourceBlock5472XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5472+k) _ _ _
    (sourceBlock5472PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5472_actual_enclosure k hk)
    (sourceBlock5472TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5472Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5472XiPair k).1 := by
  decide +kernel

theorem sourceBlock5472Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5472Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5472XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5472XiPair k)).2 ≤
      sourceBlock5472Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5472_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5472+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5472+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5472Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5472+k) (sourceBlock5472XiPair k) _
    (sourceBlock5472Xi_enclosure k hk) (sourceBlock5472Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5472Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5504_bound (k : ℕ) (hk : k < 5504) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5472
  · exact sourceRoundedMidpoint_first5472_bound k h
  · have hsum : 5472+(k-5472) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5472_bound (k-5472) (by omega)

end ReciprocalXi
