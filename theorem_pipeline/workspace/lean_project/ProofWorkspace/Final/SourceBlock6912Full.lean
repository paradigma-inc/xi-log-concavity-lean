import ProofWorkspace.Final.SourceBlock6880Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6912DataFull
import ProofWorkspace.Final.EtaBlock6912Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6912XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6912+k) (sourceBlock6912PiPairs.getD k (0,0))
    (sourceEtaBatch6912Lower k, sourceEtaBatch6912Upper k)
    (sourceBlock6912TwoPairs.getD k (0,0))

theorem sourceBlock6912Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6912XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6912+k):ℂ)).re ∧
      (xi (xiGridArgument (6912+k):ℂ)).re ≤ ((sourceBlock6912XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6912+k) _ _ _
    (sourceBlock6912PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6912_actual_enclosure k hk)
    (sourceBlock6912TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6912Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6912XiPair k).1 := by
  decide +kernel

theorem sourceBlock6912Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6912Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6912XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6912XiPair k)).2 ≤
      sourceBlock6912Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6912_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6912+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6912+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6912Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6912+k) (sourceBlock6912XiPair k) _
    (sourceBlock6912Xi_enclosure k hk) (sourceBlock6912Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6912Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6944_bound (k : ℕ) (hk : k < 6944) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6912
  · exact sourceRoundedMidpoint_first6912_bound k h
  · have hsum : 6912+(k-6912) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6912_bound (k-6912) (by omega)

end ReciprocalXi
