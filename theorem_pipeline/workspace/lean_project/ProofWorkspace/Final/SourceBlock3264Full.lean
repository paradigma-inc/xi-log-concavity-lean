import ProofWorkspace.Final.SourceBlock3232Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3264DataFull
import ProofWorkspace.Final.EtaBlock3264Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3264XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3264+k) (sourceBlock3264PiPairs.getD k (0,0))
    (sourceEtaBatch3264Lower k, sourceEtaBatch3264Upper k)
    (sourceBlock3264TwoPairs.getD k (0,0))

theorem sourceBlock3264Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3264XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3264+k):ℂ)).re ∧
      (xi (xiGridArgument (3264+k):ℂ)).re ≤ ((sourceBlock3264XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3264+k) _ _ _
    (sourceBlock3264PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3264_actual_enclosure k hk)
    (sourceBlock3264TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3264Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3264XiPair k).1 := by
  decide +kernel

theorem sourceBlock3264Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3264Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3264XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3264XiPair k)).2 ≤
      sourceBlock3264Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3264_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3264+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3264+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3264Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3264+k) (sourceBlock3264XiPair k) _
    (sourceBlock3264Xi_enclosure k hk) (sourceBlock3264Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3264Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3296_bound (k : ℕ) (hk : k < 3296) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3264
  · exact sourceRoundedMidpoint_first3264_bound k h
  · have hsum : 3264+(k-3264) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3264_bound (k-3264) (by omega)

end ReciprocalXi
