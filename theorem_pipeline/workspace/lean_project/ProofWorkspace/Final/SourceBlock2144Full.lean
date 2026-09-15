import ProofWorkspace.Final.SourceBlock2112Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2144DataFull
import ProofWorkspace.Final.EtaBlock2144Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2144XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2144+k) (sourceBlock2144PiPairs.getD k (0,0))
    (sourceEtaBatch2144Lower k, sourceEtaBatch2144Upper k)
    (sourceBlock2144TwoPairs.getD k (0,0))

theorem sourceBlock2144Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2144XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2144+k):ℂ)).re ∧
      (xi (xiGridArgument (2144+k):ℂ)).re ≤ ((sourceBlock2144XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2144+k) _ _ _
    (sourceBlock2144PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2144_actual_enclosure k hk)
    (sourceBlock2144TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2144Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2144XiPair k).1 := by
  decide +kernel

theorem sourceBlock2144Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2144Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2144XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2144XiPair k)).2 ≤
      sourceBlock2144Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2144_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2144+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2144+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2144Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2144+k) (sourceBlock2144XiPair k) _
    (sourceBlock2144Xi_enclosure k hk) (sourceBlock2144Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2144Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2176_bound (k : ℕ) (hk : k < 2176) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2144
  · exact sourceRoundedMidpoint_first2144_bound k h
  · have hsum : 2144+(k-2144) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2144_bound (k-2144) (by omega)

end ReciprocalXi
