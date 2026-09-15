import ProofWorkspace.Final.SourceBlock2688Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2720DataFull
import ProofWorkspace.Final.EtaBlock2720Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2720XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2720+k) (sourceBlock2720PiPairs.getD k (0,0))
    (sourceEtaBatch2720Lower k, sourceEtaBatch2720Upper k)
    (sourceBlock2720TwoPairs.getD k (0,0))

theorem sourceBlock2720Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2720XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2720+k):ℂ)).re ∧
      (xi (xiGridArgument (2720+k):ℂ)).re ≤ ((sourceBlock2720XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2720+k) _ _ _
    (sourceBlock2720PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2720_actual_enclosure k hk)
    (sourceBlock2720TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2720Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2720XiPair k).1 := by
  decide +kernel

theorem sourceBlock2720Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2720Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2720XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2720XiPair k)).2 ≤
      sourceBlock2720Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2720_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2720+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2720+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2720Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2720+k) (sourceBlock2720XiPair k) _
    (sourceBlock2720Xi_enclosure k hk) (sourceBlock2720Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2720Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2752_bound (k : ℕ) (hk : k < 2752) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2720
  · exact sourceRoundedMidpoint_first2720_bound k h
  · have hsum : 2720+(k-2720) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2720_bound (k-2720) (by omega)

end ReciprocalXi
