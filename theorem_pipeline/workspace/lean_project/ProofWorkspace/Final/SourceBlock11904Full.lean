import ProofWorkspace.Final.SourceBlock11872Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11904DataFull
import ProofWorkspace.Final.EtaBlock11904Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11904XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11904+k) (sourceBlock11904PiPairs.getD k (0,0))
    (sourceEtaBatch11904Lower k, sourceEtaBatch11904Upper k)
    (sourceBlock11904TwoPairs.getD k (0,0))

theorem sourceBlock11904Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11904XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11904+k):ℂ)).re ∧
      (xi (xiGridArgument (11904+k):ℂ)).re ≤ ((sourceBlock11904XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11904+k) _ _ _
    (sourceBlock11904PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11904_actual_enclosure k hk)
    (sourceBlock11904TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11904Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11904XiPair k).1 := by
  decide +kernel

theorem sourceBlock11904Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11904Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11904XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11904XiPair k)).2 ≤
      sourceBlock11904Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11904_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11904+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11904+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11904Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11904+k) (sourceBlock11904XiPair k) _
    (sourceBlock11904Xi_enclosure k hk) (sourceBlock11904Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11904Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11936_bound (k : ℕ) (hk : k < 11936) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11904
  · exact sourceRoundedMidpoint_first11904_bound k h
  · have hsum : 11904+(k-11904) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11904_bound (k-11904) (by omega)

end ReciprocalXi
