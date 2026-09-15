import ProofWorkspace.Final.SourceBlock2176Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2208DataFull
import ProofWorkspace.Final.EtaBlock2208Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2208XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2208+k) (sourceBlock2208PiPairs.getD k (0,0))
    (sourceEtaBatch2208Lower k, sourceEtaBatch2208Upper k)
    (sourceBlock2208TwoPairs.getD k (0,0))

theorem sourceBlock2208Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2208XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2208+k):ℂ)).re ∧
      (xi (xiGridArgument (2208+k):ℂ)).re ≤ ((sourceBlock2208XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2208+k) _ _ _
    (sourceBlock2208PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2208_actual_enclosure k hk)
    (sourceBlock2208TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2208Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2208XiPair k).1 := by
  decide +kernel

theorem sourceBlock2208Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2208Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2208XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2208XiPair k)).2 ≤
      sourceBlock2208Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2208_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2208+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2208+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2208Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2208+k) (sourceBlock2208XiPair k) _
    (sourceBlock2208Xi_enclosure k hk) (sourceBlock2208Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2208Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2240_bound (k : ℕ) (hk : k < 2240) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2208
  · exact sourceRoundedMidpoint_first2208_bound k h
  · have hsum : 2208+(k-2208) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2208_bound (k-2208) (by omega)

end ReciprocalXi
