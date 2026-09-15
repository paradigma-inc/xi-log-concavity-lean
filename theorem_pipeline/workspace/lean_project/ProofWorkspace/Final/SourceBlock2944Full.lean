import ProofWorkspace.Final.SourceBlock2912Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2944DataFull
import ProofWorkspace.Final.EtaBlock2944Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2944XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2944+k) (sourceBlock2944PiPairs.getD k (0,0))
    (sourceEtaBatch2944Lower k, sourceEtaBatch2944Upper k)
    (sourceBlock2944TwoPairs.getD k (0,0))

theorem sourceBlock2944Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2944XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2944+k):ℂ)).re ∧
      (xi (xiGridArgument (2944+k):ℂ)).re ≤ ((sourceBlock2944XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2944+k) _ _ _
    (sourceBlock2944PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2944_actual_enclosure k hk)
    (sourceBlock2944TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2944Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2944XiPair k).1 := by
  decide +kernel

theorem sourceBlock2944Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2944Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2944XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2944XiPair k)).2 ≤
      sourceBlock2944Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2944_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2944+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2944+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2944Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2944+k) (sourceBlock2944XiPair k) _
    (sourceBlock2944Xi_enclosure k hk) (sourceBlock2944Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2944Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2976_bound (k : ℕ) (hk : k < 2976) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2944
  · exact sourceRoundedMidpoint_first2944_bound k h
  · have hsum : 2944+(k-2944) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2944_bound (k-2944) (by omega)

end ReciprocalXi
