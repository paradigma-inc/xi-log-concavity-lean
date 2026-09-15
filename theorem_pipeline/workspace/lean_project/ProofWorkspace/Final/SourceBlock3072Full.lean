import ProofWorkspace.Final.SourceBlock3040Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3072DataFull
import ProofWorkspace.Final.EtaBlock3072Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3072XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3072+k) (sourceBlock3072PiPairs.getD k (0,0))
    (sourceEtaBatch3072Lower k, sourceEtaBatch3072Upper k)
    (sourceBlock3072TwoPairs.getD k (0,0))

theorem sourceBlock3072Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3072XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3072+k):ℂ)).re ∧
      (xi (xiGridArgument (3072+k):ℂ)).re ≤ ((sourceBlock3072XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3072+k) _ _ _
    (sourceBlock3072PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3072_actual_enclosure k hk)
    (sourceBlock3072TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3072Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3072XiPair k).1 := by
  decide +kernel

theorem sourceBlock3072Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3072Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3072XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3072XiPair k)).2 ≤
      sourceBlock3072Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3072_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3072+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3072+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3072Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3072+k) (sourceBlock3072XiPair k) _
    (sourceBlock3072Xi_enclosure k hk) (sourceBlock3072Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3072Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3104_bound (k : ℕ) (hk : k < 3104) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3072
  · exact sourceRoundedMidpoint_first3072_bound k h
  · have hsum : 3072+(k-3072) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3072_bound (k-3072) (by omega)

end ReciprocalXi
