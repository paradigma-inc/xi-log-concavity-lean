import ProofWorkspace.Final.SourceBlock6176Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6208DataFull
import ProofWorkspace.Final.EtaBlock6208Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6208XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6208+k) (sourceBlock6208PiPairs.getD k (0,0))
    (sourceEtaBatch6208Lower k, sourceEtaBatch6208Upper k)
    (sourceBlock6208TwoPairs.getD k (0,0))

theorem sourceBlock6208Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6208XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6208+k):ℂ)).re ∧
      (xi (xiGridArgument (6208+k):ℂ)).re ≤ ((sourceBlock6208XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6208+k) _ _ _
    (sourceBlock6208PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6208_actual_enclosure k hk)
    (sourceBlock6208TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6208Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6208XiPair k).1 := by
  decide +kernel

theorem sourceBlock6208Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6208Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6208XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6208XiPair k)).2 ≤
      sourceBlock6208Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6208_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6208+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6208+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6208Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6208+k) (sourceBlock6208XiPair k) _
    (sourceBlock6208Xi_enclosure k hk) (sourceBlock6208Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6208Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6240_bound (k : ℕ) (hk : k < 6240) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6208
  · exact sourceRoundedMidpoint_first6208_bound k h
  · have hsum : 6208+(k-6208) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6208_bound (k-6208) (by omega)

end ReciprocalXi
