import ProofWorkspace.Final.SourceBlock3840Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3872DataFull
import ProofWorkspace.Final.EtaBlock3872Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3872XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3872+k) (sourceBlock3872PiPairs.getD k (0,0))
    (sourceEtaBatch3872Lower k, sourceEtaBatch3872Upper k)
    (sourceBlock3872TwoPairs.getD k (0,0))

theorem sourceBlock3872Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3872XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3872+k):ℂ)).re ∧
      (xi (xiGridArgument (3872+k):ℂ)).re ≤ ((sourceBlock3872XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3872+k) _ _ _
    (sourceBlock3872PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3872_actual_enclosure k hk)
    (sourceBlock3872TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3872Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3872XiPair k).1 := by
  decide +kernel

theorem sourceBlock3872Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3872Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3872XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3872XiPair k)).2 ≤
      sourceBlock3872Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3872_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3872+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3872+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3872Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3872+k) (sourceBlock3872XiPair k) _
    (sourceBlock3872Xi_enclosure k hk) (sourceBlock3872Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3872Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3904_bound (k : ℕ) (hk : k < 3904) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3872
  · exact sourceRoundedMidpoint_first3872_bound k h
  · have hsum : 3872+(k-3872) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3872_bound (k-3872) (by omega)

end ReciprocalXi
