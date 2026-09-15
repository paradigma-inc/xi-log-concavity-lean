import ProofWorkspace.Final.SourceBlock2656Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2688DataFull
import ProofWorkspace.Final.EtaBlock2688Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2688XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2688+k) (sourceBlock2688PiPairs.getD k (0,0))
    (sourceEtaBatch2688Lower k, sourceEtaBatch2688Upper k)
    (sourceBlock2688TwoPairs.getD k (0,0))

theorem sourceBlock2688Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2688XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2688+k):ℂ)).re ∧
      (xi (xiGridArgument (2688+k):ℂ)).re ≤ ((sourceBlock2688XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2688+k) _ _ _
    (sourceBlock2688PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2688_actual_enclosure k hk)
    (sourceBlock2688TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2688Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2688XiPair k).1 := by
  decide +kernel

theorem sourceBlock2688Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2688Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2688XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2688XiPair k)).2 ≤
      sourceBlock2688Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2688_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2688+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2688+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2688Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2688+k) (sourceBlock2688XiPair k) _
    (sourceBlock2688Xi_enclosure k hk) (sourceBlock2688Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2688Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2720_bound (k : ℕ) (hk : k < 2720) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2688
  · exact sourceRoundedMidpoint_first2688_bound k h
  · have hsum : 2688+(k-2688) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2688_bound (k-2688) (by omega)

end ReciprocalXi
