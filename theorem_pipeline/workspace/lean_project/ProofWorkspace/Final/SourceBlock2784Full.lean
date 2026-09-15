import ProofWorkspace.Final.SourceBlock2752Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2784DataFull
import ProofWorkspace.Final.EtaBlock2784Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2784XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2784+k) (sourceBlock2784PiPairs.getD k (0,0))
    (sourceEtaBatch2784Lower k, sourceEtaBatch2784Upper k)
    (sourceBlock2784TwoPairs.getD k (0,0))

theorem sourceBlock2784Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2784XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2784+k):ℂ)).re ∧
      (xi (xiGridArgument (2784+k):ℂ)).re ≤ ((sourceBlock2784XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2784+k) _ _ _
    (sourceBlock2784PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2784_actual_enclosure k hk)
    (sourceBlock2784TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2784Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2784XiPair k).1 := by
  decide +kernel

theorem sourceBlock2784Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2784Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2784XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2784XiPair k)).2 ≤
      sourceBlock2784Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2784_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2784+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2784+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2784Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2784+k) (sourceBlock2784XiPair k) _
    (sourceBlock2784Xi_enclosure k hk) (sourceBlock2784Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2784Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2816_bound (k : ℕ) (hk : k < 2816) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2784
  · exact sourceRoundedMidpoint_first2784_bound k h
  · have hsum : 2784+(k-2784) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2784_bound (k-2784) (by omega)

end ReciprocalXi
