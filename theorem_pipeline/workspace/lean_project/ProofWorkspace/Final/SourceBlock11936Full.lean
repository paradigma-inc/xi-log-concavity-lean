import ProofWorkspace.Final.SourceBlock11904Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11936DataFull
import ProofWorkspace.Final.EtaBlock11936Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11936XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11936+k) (sourceBlock11936PiPairs.getD k (0,0))
    (sourceEtaBatch11936Lower k, sourceEtaBatch11936Upper k)
    (sourceBlock11936TwoPairs.getD k (0,0))

theorem sourceBlock11936Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11936XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11936+k):ℂ)).re ∧
      (xi (xiGridArgument (11936+k):ℂ)).re ≤ ((sourceBlock11936XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11936+k) _ _ _
    (sourceBlock11936PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11936_actual_enclosure k hk)
    (sourceBlock11936TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11936Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11936XiPair k).1 := by
  decide +kernel

theorem sourceBlock11936Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11936Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11936XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11936XiPair k)).2 ≤
      sourceBlock11936Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11936_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11936+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11936+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11936Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11936+k) (sourceBlock11936XiPair k) _
    (sourceBlock11936Xi_enclosure k hk) (sourceBlock11936Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11936Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11968_bound (k : ℕ) (hk : k < 11968) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11936
  · exact sourceRoundedMidpoint_first11936_bound k h
  · have hsum : 11936+(k-11936) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11936_bound (k-11936) (by omega)

end ReciprocalXi
