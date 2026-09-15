import ProofWorkspace.Final.SourceBlock3328Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3360DataFull
import ProofWorkspace.Final.EtaBlock3360Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3360XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3360+k) (sourceBlock3360PiPairs.getD k (0,0))
    (sourceEtaBatch3360Lower k, sourceEtaBatch3360Upper k)
    (sourceBlock3360TwoPairs.getD k (0,0))

theorem sourceBlock3360Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3360XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3360+k):ℂ)).re ∧
      (xi (xiGridArgument (3360+k):ℂ)).re ≤ ((sourceBlock3360XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3360+k) _ _ _
    (sourceBlock3360PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3360_actual_enclosure k hk)
    (sourceBlock3360TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3360Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3360XiPair k).1 := by
  decide +kernel

theorem sourceBlock3360Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3360Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3360XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3360XiPair k)).2 ≤
      sourceBlock3360Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3360_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3360+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3360+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3360Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3360+k) (sourceBlock3360XiPair k) _
    (sourceBlock3360Xi_enclosure k hk) (sourceBlock3360Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3360Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3392_bound (k : ℕ) (hk : k < 3392) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3360
  · exact sourceRoundedMidpoint_first3360_bound k h
  · have hsum : 3360+(k-3360) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3360_bound (k-3360) (by omega)

end ReciprocalXi
