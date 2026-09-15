import ProofWorkspace.Final.SourceBlock2592Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2624DataFull
import ProofWorkspace.Final.EtaBlock2624Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2624XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2624+k) (sourceBlock2624PiPairs.getD k (0,0))
    (sourceEtaBatch2624Lower k, sourceEtaBatch2624Upper k)
    (sourceBlock2624TwoPairs.getD k (0,0))

theorem sourceBlock2624Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2624XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2624+k):ℂ)).re ∧
      (xi (xiGridArgument (2624+k):ℂ)).re ≤ ((sourceBlock2624XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2624+k) _ _ _
    (sourceBlock2624PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2624_actual_enclosure k hk)
    (sourceBlock2624TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2624Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2624XiPair k).1 := by
  decide +kernel

theorem sourceBlock2624Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2624Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2624XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2624XiPair k)).2 ≤
      sourceBlock2624Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2624_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2624+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2624+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2624Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2624+k) (sourceBlock2624XiPair k) _
    (sourceBlock2624Xi_enclosure k hk) (sourceBlock2624Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2624Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2656_bound (k : ℕ) (hk : k < 2656) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2624
  · exact sourceRoundedMidpoint_first2624_bound k h
  · have hsum : 2624+(k-2624) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2624_bound (k-2624) (by omega)

end ReciprocalXi
