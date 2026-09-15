import ProofWorkspace.Final.SourceBlock7008Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7040DataFull
import ProofWorkspace.Final.EtaBlock7040Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7040XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7040+k) (sourceBlock7040PiPairs.getD k (0,0))
    (sourceEtaBatch7040Lower k, sourceEtaBatch7040Upper k)
    (sourceBlock7040TwoPairs.getD k (0,0))

theorem sourceBlock7040Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7040XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7040+k):ℂ)).re ∧
      (xi (xiGridArgument (7040+k):ℂ)).re ≤ ((sourceBlock7040XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7040+k) _ _ _
    (sourceBlock7040PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7040_actual_enclosure k hk)
    (sourceBlock7040TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7040Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7040XiPair k).1 := by
  decide +kernel

theorem sourceBlock7040Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7040Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7040XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7040XiPair k)).2 ≤
      sourceBlock7040Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7040_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7040+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7040+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7040Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7040+k) (sourceBlock7040XiPair k) _
    (sourceBlock7040Xi_enclosure k hk) (sourceBlock7040Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7040Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7072_bound (k : ℕ) (hk : k < 7072) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7040
  · exact sourceRoundedMidpoint_first7040_bound k h
  · have hsum : 7040+(k-7040) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7040_bound (k-7040) (by omega)

end ReciprocalXi
