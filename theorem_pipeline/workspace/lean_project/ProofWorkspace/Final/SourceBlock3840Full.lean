import ProofWorkspace.Final.SourceBlock3808Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3840DataFull
import ProofWorkspace.Final.EtaBlock3840Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3840XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3840+k) (sourceBlock3840PiPairs.getD k (0,0))
    (sourceEtaBatch3840Lower k, sourceEtaBatch3840Upper k)
    (sourceBlock3840TwoPairs.getD k (0,0))

theorem sourceBlock3840Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3840XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3840+k):ℂ)).re ∧
      (xi (xiGridArgument (3840+k):ℂ)).re ≤ ((sourceBlock3840XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3840+k) _ _ _
    (sourceBlock3840PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3840_actual_enclosure k hk)
    (sourceBlock3840TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3840Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3840XiPair k).1 := by
  decide +kernel

theorem sourceBlock3840Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3840Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3840XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3840XiPair k)).2 ≤
      sourceBlock3840Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3840_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3840+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3840+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3840Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3840+k) (sourceBlock3840XiPair k) _
    (sourceBlock3840Xi_enclosure k hk) (sourceBlock3840Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3840Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3872_bound (k : ℕ) (hk : k < 3872) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3840
  · exact sourceRoundedMidpoint_first3840_bound k h
  · have hsum : 3840+(k-3840) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3840_bound (k-3840) (by omega)

end ReciprocalXi
