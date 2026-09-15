import ProofWorkspace.Final.SourceBlock2624Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2656DataFull
import ProofWorkspace.Final.EtaBlock2656Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2656XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2656+k) (sourceBlock2656PiPairs.getD k (0,0))
    (sourceEtaBatch2656Lower k, sourceEtaBatch2656Upper k)
    (sourceBlock2656TwoPairs.getD k (0,0))

theorem sourceBlock2656Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2656XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2656+k):ℂ)).re ∧
      (xi (xiGridArgument (2656+k):ℂ)).re ≤ ((sourceBlock2656XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2656+k) _ _ _
    (sourceBlock2656PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2656_actual_enclosure k hk)
    (sourceBlock2656TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2656Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2656XiPair k).1 := by
  decide +kernel

theorem sourceBlock2656Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2656Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2656XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2656XiPair k)).2 ≤
      sourceBlock2656Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2656_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2656+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2656+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2656Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2656+k) (sourceBlock2656XiPair k) _
    (sourceBlock2656Xi_enclosure k hk) (sourceBlock2656Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2656Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2688_bound (k : ℕ) (hk : k < 2688) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2656
  · exact sourceRoundedMidpoint_first2656_bound k h
  · have hsum : 2656+(k-2656) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2656_bound (k-2656) (by omega)

end ReciprocalXi
