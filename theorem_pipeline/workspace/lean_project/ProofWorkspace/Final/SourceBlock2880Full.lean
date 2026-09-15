import ProofWorkspace.Final.SourceBlock2848Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2880DataFull
import ProofWorkspace.Final.EtaBlock2880Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2880XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2880+k) (sourceBlock2880PiPairs.getD k (0,0))
    (sourceEtaBatch2880Lower k, sourceEtaBatch2880Upper k)
    (sourceBlock2880TwoPairs.getD k (0,0))

theorem sourceBlock2880Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2880XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2880+k):ℂ)).re ∧
      (xi (xiGridArgument (2880+k):ℂ)).re ≤ ((sourceBlock2880XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2880+k) _ _ _
    (sourceBlock2880PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2880_actual_enclosure k hk)
    (sourceBlock2880TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2880Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2880XiPair k).1 := by
  decide +kernel

theorem sourceBlock2880Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2880Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2880XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2880XiPair k)).2 ≤
      sourceBlock2880Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2880_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2880+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2880+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2880Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2880+k) (sourceBlock2880XiPair k) _
    (sourceBlock2880Xi_enclosure k hk) (sourceBlock2880Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2880Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2912_bound (k : ℕ) (hk : k < 2912) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2880
  · exact sourceRoundedMidpoint_first2880_bound k h
  · have hsum : 2880+(k-2880) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2880_bound (k-2880) (by omega)

end ReciprocalXi
