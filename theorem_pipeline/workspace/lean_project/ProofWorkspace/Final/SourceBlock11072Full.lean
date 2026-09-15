import ProofWorkspace.Final.SourceBlock11040Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11072DataFull
import ProofWorkspace.Final.EtaBlock11072Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11072XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11072+k) (sourceBlock11072PiPairs.getD k (0,0))
    (sourceEtaBatch11072Lower k, sourceEtaBatch11072Upper k)
    (sourceBlock11072TwoPairs.getD k (0,0))

theorem sourceBlock11072Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11072XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11072+k):ℂ)).re ∧
      (xi (xiGridArgument (11072+k):ℂ)).re ≤ ((sourceBlock11072XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11072+k) _ _ _
    (sourceBlock11072PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11072_actual_enclosure k hk)
    (sourceBlock11072TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11072Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11072XiPair k).1 := by
  decide +kernel

theorem sourceBlock11072Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11072Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11072XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11072XiPair k)).2 ≤
      sourceBlock11072Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11072_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11072+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11072+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11072Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11072+k) (sourceBlock11072XiPair k) _
    (sourceBlock11072Xi_enclosure k hk) (sourceBlock11072Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11072Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11104_bound (k : ℕ) (hk : k < 11104) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11072
  · exact sourceRoundedMidpoint_first11072_bound k h
  · have hsum : 11072+(k-11072) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11072_bound (k-11072) (by omega)

end ReciprocalXi
