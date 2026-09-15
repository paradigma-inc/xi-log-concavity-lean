import ProofWorkspace.Final.SourceBlock2464Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2496DataFull
import ProofWorkspace.Final.EtaBlock2496Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2496XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2496+k) (sourceBlock2496PiPairs.getD k (0,0))
    (sourceEtaBatch2496Lower k, sourceEtaBatch2496Upper k)
    (sourceBlock2496TwoPairs.getD k (0,0))

theorem sourceBlock2496Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2496XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2496+k):ℂ)).re ∧
      (xi (xiGridArgument (2496+k):ℂ)).re ≤ ((sourceBlock2496XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2496+k) _ _ _
    (sourceBlock2496PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2496_actual_enclosure k hk)
    (sourceBlock2496TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2496Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2496XiPair k).1 := by
  decide +kernel

theorem sourceBlock2496Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2496Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2496XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2496XiPair k)).2 ≤
      sourceBlock2496Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2496_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2496+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2496+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2496Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2496+k) (sourceBlock2496XiPair k) _
    (sourceBlock2496Xi_enclosure k hk) (sourceBlock2496Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2496Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2528_bound (k : ℕ) (hk : k < 2528) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2496
  · exact sourceRoundedMidpoint_first2496_bound k h
  · have hsum : 2496+(k-2496) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2496_bound (k-2496) (by omega)

end ReciprocalXi
