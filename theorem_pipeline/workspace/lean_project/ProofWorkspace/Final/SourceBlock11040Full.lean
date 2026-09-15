import ProofWorkspace.Final.SourceBlock11008Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11040DataFull
import ProofWorkspace.Final.EtaBlock11040Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11040XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11040+k) (sourceBlock11040PiPairs.getD k (0,0))
    (sourceEtaBatch11040Lower k, sourceEtaBatch11040Upper k)
    (sourceBlock11040TwoPairs.getD k (0,0))

theorem sourceBlock11040Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11040XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11040+k):ℂ)).re ∧
      (xi (xiGridArgument (11040+k):ℂ)).re ≤ ((sourceBlock11040XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11040+k) _ _ _
    (sourceBlock11040PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11040_actual_enclosure k hk)
    (sourceBlock11040TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11040Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11040XiPair k).1 := by
  decide +kernel

theorem sourceBlock11040Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11040Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11040XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11040XiPair k)).2 ≤
      sourceBlock11040Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11040_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11040+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11040+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11040Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11040+k) (sourceBlock11040XiPair k) _
    (sourceBlock11040Xi_enclosure k hk) (sourceBlock11040Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11040Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11072_bound (k : ℕ) (hk : k < 11072) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11040
  · exact sourceRoundedMidpoint_first11040_bound k h
  · have hsum : 11040+(k-11040) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11040_bound (k-11040) (by omega)

end ReciprocalXi
