import ProofWorkspace.Final.SourceBlock11232Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11264DataFull
import ProofWorkspace.Final.EtaBlock11264Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11264XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11264+k) (sourceBlock11264PiPairs.getD k (0,0))
    (sourceEtaBatch11264Lower k, sourceEtaBatch11264Upper k)
    (sourceBlock11264TwoPairs.getD k (0,0))

theorem sourceBlock11264Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11264XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11264+k):ℂ)).re ∧
      (xi (xiGridArgument (11264+k):ℂ)).re ≤ ((sourceBlock11264XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11264+k) _ _ _
    (sourceBlock11264PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11264_actual_enclosure k hk)
    (sourceBlock11264TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11264Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11264XiPair k).1 := by
  decide +kernel

theorem sourceBlock11264Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11264Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11264XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11264XiPair k)).2 ≤
      sourceBlock11264Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11264_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11264+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11264+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11264Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11264+k) (sourceBlock11264XiPair k) _
    (sourceBlock11264Xi_enclosure k hk) (sourceBlock11264Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11264Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11296_bound (k : ℕ) (hk : k < 11296) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11264
  · exact sourceRoundedMidpoint_first11264_bound k h
  · have hsum : 11264+(k-11264) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11264_bound (k-11264) (by omega)

end ReciprocalXi
