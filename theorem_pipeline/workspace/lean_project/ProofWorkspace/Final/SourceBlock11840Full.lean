import ProofWorkspace.Final.SourceBlock11808Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11840DataFull
import ProofWorkspace.Final.EtaBlock11840Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11840XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11840+k) (sourceBlock11840PiPairs.getD k (0,0))
    (sourceEtaBatch11840Lower k, sourceEtaBatch11840Upper k)
    (sourceBlock11840TwoPairs.getD k (0,0))

theorem sourceBlock11840Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11840XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11840+k):ℂ)).re ∧
      (xi (xiGridArgument (11840+k):ℂ)).re ≤ ((sourceBlock11840XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11840+k) _ _ _
    (sourceBlock11840PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11840_actual_enclosure k hk)
    (sourceBlock11840TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11840Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11840XiPair k).1 := by
  decide +kernel

theorem sourceBlock11840Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11840Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11840XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11840XiPair k)).2 ≤
      sourceBlock11840Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11840_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11840+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11840+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11840Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11840+k) (sourceBlock11840XiPair k) _
    (sourceBlock11840Xi_enclosure k hk) (sourceBlock11840Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11840Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11872_bound (k : ℕ) (hk : k < 11872) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11840
  · exact sourceRoundedMidpoint_first11840_bound k h
  · have hsum : 11840+(k-11840) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11840_bound (k-11840) (by omega)

end ReciprocalXi
