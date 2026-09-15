import ProofWorkspace.Final.SourceBlock10880Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10912DataFull
import ProofWorkspace.Final.EtaBlock10912Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10912XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10912+k) (sourceBlock10912PiPairs.getD k (0,0))
    (sourceEtaBatch10912Lower k, sourceEtaBatch10912Upper k)
    (sourceBlock10912TwoPairs.getD k (0,0))

theorem sourceBlock10912Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10912XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10912+k):ℂ)).re ∧
      (xi (xiGridArgument (10912+k):ℂ)).re ≤ ((sourceBlock10912XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10912+k) _ _ _
    (sourceBlock10912PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10912_actual_enclosure k hk)
    (sourceBlock10912TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10912Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10912XiPair k).1 := by
  decide +kernel

theorem sourceBlock10912Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10912Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10912XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10912XiPair k)).2 ≤
      sourceBlock10912Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10912_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10912+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10912+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10912Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10912+k) (sourceBlock10912XiPair k) _
    (sourceBlock10912Xi_enclosure k hk) (sourceBlock10912Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10912Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10944_bound (k : ℕ) (hk : k < 10944) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10912
  · exact sourceRoundedMidpoint_first10912_bound k h
  · have hsum : 10912+(k-10912) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10912_bound (k-10912) (by omega)

end ReciprocalXi
