import ProofWorkspace.Final.SourceBlock3776Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3808DataFull
import ProofWorkspace.Final.EtaBlock3808Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3808XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3808+k) (sourceBlock3808PiPairs.getD k (0,0))
    (sourceEtaBatch3808Lower k, sourceEtaBatch3808Upper k)
    (sourceBlock3808TwoPairs.getD k (0,0))

theorem sourceBlock3808Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3808XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3808+k):ℂ)).re ∧
      (xi (xiGridArgument (3808+k):ℂ)).re ≤ ((sourceBlock3808XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3808+k) _ _ _
    (sourceBlock3808PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3808_actual_enclosure k hk)
    (sourceBlock3808TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3808Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3808XiPair k).1 := by
  decide +kernel

theorem sourceBlock3808Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3808Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3808XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3808XiPair k)).2 ≤
      sourceBlock3808Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3808_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3808+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3808+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3808Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3808+k) (sourceBlock3808XiPair k) _
    (sourceBlock3808Xi_enclosure k hk) (sourceBlock3808Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3808Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3840_bound (k : ℕ) (hk : k < 3840) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3808
  · exact sourceRoundedMidpoint_first3808_bound k h
  · have hsum : 3808+(k-3808) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3808_bound (k-3808) (by omega)

end ReciprocalXi
