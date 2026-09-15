import ProofWorkspace.Final.SourceBlock11616Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11648DataFull
import ProofWorkspace.Final.EtaBlock11648Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11648XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11648+k) (sourceBlock11648PiPairs.getD k (0,0))
    (sourceEtaBatch11648Lower k, sourceEtaBatch11648Upper k)
    (sourceBlock11648TwoPairs.getD k (0,0))

theorem sourceBlock11648Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11648XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11648+k):ℂ)).re ∧
      (xi (xiGridArgument (11648+k):ℂ)).re ≤ ((sourceBlock11648XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11648+k) _ _ _
    (sourceBlock11648PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11648_actual_enclosure k hk)
    (sourceBlock11648TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11648Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11648XiPair k).1 := by
  decide +kernel

theorem sourceBlock11648Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11648Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11648XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11648XiPair k)).2 ≤
      sourceBlock11648Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11648_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11648+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11648+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11648Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11648+k) (sourceBlock11648XiPair k) _
    (sourceBlock11648Xi_enclosure k hk) (sourceBlock11648Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11648Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11680_bound (k : ℕ) (hk : k < 11680) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11648
  · exact sourceRoundedMidpoint_first11648_bound k h
  · have hsum : 11648+(k-11648) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11648_bound (k-11648) (by omega)

end ReciprocalXi
