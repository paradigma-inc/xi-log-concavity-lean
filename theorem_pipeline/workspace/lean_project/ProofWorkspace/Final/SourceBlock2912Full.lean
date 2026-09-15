import ProofWorkspace.Final.SourceBlock2880Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2912DataFull
import ProofWorkspace.Final.EtaBlock2912Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2912XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2912+k) (sourceBlock2912PiPairs.getD k (0,0))
    (sourceEtaBatch2912Lower k, sourceEtaBatch2912Upper k)
    (sourceBlock2912TwoPairs.getD k (0,0))

theorem sourceBlock2912Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2912XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2912+k):ℂ)).re ∧
      (xi (xiGridArgument (2912+k):ℂ)).re ≤ ((sourceBlock2912XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2912+k) _ _ _
    (sourceBlock2912PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2912_actual_enclosure k hk)
    (sourceBlock2912TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2912Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2912XiPair k).1 := by
  decide +kernel

theorem sourceBlock2912Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2912Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2912XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2912XiPair k)).2 ≤
      sourceBlock2912Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2912_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2912+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2912+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2912Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2912+k) (sourceBlock2912XiPair k) _
    (sourceBlock2912Xi_enclosure k hk) (sourceBlock2912Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2912Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2944_bound (k : ℕ) (hk : k < 2944) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2912
  · exact sourceRoundedMidpoint_first2912_bound k h
  · have hsum : 2912+(k-2912) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2912_bound (k-2912) (by omega)

end ReciprocalXi
