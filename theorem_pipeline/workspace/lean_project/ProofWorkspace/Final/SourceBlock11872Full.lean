import ProofWorkspace.Final.SourceBlock11840Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11872DataFull
import ProofWorkspace.Final.EtaBlock11872Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11872XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11872+k) (sourceBlock11872PiPairs.getD k (0,0))
    (sourceEtaBatch11872Lower k, sourceEtaBatch11872Upper k)
    (sourceBlock11872TwoPairs.getD k (0,0))

theorem sourceBlock11872Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11872XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11872+k):ℂ)).re ∧
      (xi (xiGridArgument (11872+k):ℂ)).re ≤ ((sourceBlock11872XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11872+k) _ _ _
    (sourceBlock11872PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11872_actual_enclosure k hk)
    (sourceBlock11872TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11872Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11872XiPair k).1 := by
  decide +kernel

theorem sourceBlock11872Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11872Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11872XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11872XiPair k)).2 ≤
      sourceBlock11872Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11872_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11872+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11872+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11872Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11872+k) (sourceBlock11872XiPair k) _
    (sourceBlock11872Xi_enclosure k hk) (sourceBlock11872Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11872Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11904_bound (k : ℕ) (hk : k < 11904) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11872
  · exact sourceRoundedMidpoint_first11872_bound k h
  · have hsum : 11872+(k-11872) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11872_bound (k-11872) (by omega)

end ReciprocalXi
