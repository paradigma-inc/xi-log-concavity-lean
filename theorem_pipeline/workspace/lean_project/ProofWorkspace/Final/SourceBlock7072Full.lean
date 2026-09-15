import ProofWorkspace.Final.SourceBlock7040Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7072DataFull
import ProofWorkspace.Final.EtaBlock7072Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7072XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7072+k) (sourceBlock7072PiPairs.getD k (0,0))
    (sourceEtaBatch7072Lower k, sourceEtaBatch7072Upper k)
    (sourceBlock7072TwoPairs.getD k (0,0))

theorem sourceBlock7072Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7072XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7072+k):ℂ)).re ∧
      (xi (xiGridArgument (7072+k):ℂ)).re ≤ ((sourceBlock7072XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7072+k) _ _ _
    (sourceBlock7072PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7072_actual_enclosure k hk)
    (sourceBlock7072TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7072Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7072XiPair k).1 := by
  decide +kernel

theorem sourceBlock7072Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7072Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7072XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7072XiPair k)).2 ≤
      sourceBlock7072Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7072_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7072+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7072+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7072Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7072+k) (sourceBlock7072XiPair k) _
    (sourceBlock7072Xi_enclosure k hk) (sourceBlock7072Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7072Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7104_bound (k : ℕ) (hk : k < 7104) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7072
  · exact sourceRoundedMidpoint_first7072_bound k h
  · have hsum : 7072+(k-7072) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7072_bound (k-7072) (by omega)

end ReciprocalXi
