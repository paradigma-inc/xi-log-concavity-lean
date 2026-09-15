import ProofWorkspace.Final.SourceBlock7232Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7264DataFull
import ProofWorkspace.Final.EtaBlock7264Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7264XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7264+k) (sourceBlock7264PiPairs.getD k (0,0))
    (sourceEtaBatch7264Lower k, sourceEtaBatch7264Upper k)
    (sourceBlock7264TwoPairs.getD k (0,0))

theorem sourceBlock7264Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7264XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7264+k):ℂ)).re ∧
      (xi (xiGridArgument (7264+k):ℂ)).re ≤ ((sourceBlock7264XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7264+k) _ _ _
    (sourceBlock7264PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7264_actual_enclosure k hk)
    (sourceBlock7264TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7264Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7264XiPair k).1 := by
  decide +kernel

theorem sourceBlock7264Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7264Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7264XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7264XiPair k)).2 ≤
      sourceBlock7264Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7264_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7264+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7264+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7264Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7264+k) (sourceBlock7264XiPair k) _
    (sourceBlock7264Xi_enclosure k hk) (sourceBlock7264Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7264Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7296_bound (k : ℕ) (hk : k < 7296) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7264
  · exact sourceRoundedMidpoint_first7264_bound k h
  · have hsum : 7264+(k-7264) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7264_bound (k-7264) (by omega)

end ReciprocalXi
