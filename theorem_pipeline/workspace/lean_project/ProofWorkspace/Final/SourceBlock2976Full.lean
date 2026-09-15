import ProofWorkspace.Final.SourceBlock2944Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2976DataFull
import ProofWorkspace.Final.EtaBlock2976Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2976XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2976+k) (sourceBlock2976PiPairs.getD k (0,0))
    (sourceEtaBatch2976Lower k, sourceEtaBatch2976Upper k)
    (sourceBlock2976TwoPairs.getD k (0,0))

theorem sourceBlock2976Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2976XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2976+k):ℂ)).re ∧
      (xi (xiGridArgument (2976+k):ℂ)).re ≤ ((sourceBlock2976XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2976+k) _ _ _
    (sourceBlock2976PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2976_actual_enclosure k hk)
    (sourceBlock2976TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2976Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2976XiPair k).1 := by
  decide +kernel

theorem sourceBlock2976Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2976Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2976XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2976XiPair k)).2 ≤
      sourceBlock2976Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2976_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2976+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2976+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2976Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2976+k) (sourceBlock2976XiPair k) _
    (sourceBlock2976Xi_enclosure k hk) (sourceBlock2976Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2976Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3008_bound (k : ℕ) (hk : k < 3008) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2976
  · exact sourceRoundedMidpoint_first2976_bound k h
  · have hsum : 2976+(k-2976) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2976_bound (k-2976) (by omega)

end ReciprocalXi
