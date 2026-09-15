import ProofWorkspace.Final.SourceBlock11776Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11808DataFull
import ProofWorkspace.Final.EtaBlock11808Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11808XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11808+k) (sourceBlock11808PiPairs.getD k (0,0))
    (sourceEtaBatch11808Lower k, sourceEtaBatch11808Upper k)
    (sourceBlock11808TwoPairs.getD k (0,0))

theorem sourceBlock11808Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11808XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11808+k):ℂ)).re ∧
      (xi (xiGridArgument (11808+k):ℂ)).re ≤ ((sourceBlock11808XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11808+k) _ _ _
    (sourceBlock11808PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11808_actual_enclosure k hk)
    (sourceBlock11808TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11808Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11808XiPair k).1 := by
  decide +kernel

theorem sourceBlock11808Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11808Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11808XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11808XiPair k)).2 ≤
      sourceBlock11808Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11808_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11808+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11808+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11808Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11808+k) (sourceBlock11808XiPair k) _
    (sourceBlock11808Xi_enclosure k hk) (sourceBlock11808Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11808Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11840_bound (k : ℕ) (hk : k < 11840) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11808
  · exact sourceRoundedMidpoint_first11808_bound k h
  · have hsum : 11808+(k-11808) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11808_bound (k-11808) (by omega)

end ReciprocalXi
