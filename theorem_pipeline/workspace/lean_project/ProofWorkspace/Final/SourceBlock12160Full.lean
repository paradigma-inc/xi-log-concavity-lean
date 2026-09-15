import ProofWorkspace.Final.SourceBlock12128Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12160DataFull
import ProofWorkspace.Final.EtaBlock12160Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12160XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12160+k) (sourceBlock12160PiPairs.getD k (0,0))
    (sourceEtaBatch12160Lower k, sourceEtaBatch12160Upper k)
    (sourceBlock12160TwoPairs.getD k (0,0))

theorem sourceBlock12160Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12160XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12160+k):ℂ)).re ∧
      (xi (xiGridArgument (12160+k):ℂ)).re ≤ ((sourceBlock12160XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12160+k) _ _ _
    (sourceBlock12160PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12160_actual_enclosure k hk)
    (sourceBlock12160TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12160Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12160XiPair k).1 := by
  decide +kernel

theorem sourceBlock12160Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12160Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12160XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12160XiPair k)).2 ≤
      sourceBlock12160Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12160_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12160+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12160+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12160Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12160+k) (sourceBlock12160XiPair k) _
    (sourceBlock12160Xi_enclosure k hk) (sourceBlock12160Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12160Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12192_bound (k : ℕ) (hk : k < 12192) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12160
  · exact sourceRoundedMidpoint_first12160_bound k h
  · have hsum : 12160+(k-12160) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12160_bound (k-12160) (by omega)

end ReciprocalXi
