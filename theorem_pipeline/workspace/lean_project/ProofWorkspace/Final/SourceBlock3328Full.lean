import ProofWorkspace.Final.SourceBlock3296Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3328DataFull
import ProofWorkspace.Final.EtaBlock3328Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3328XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3328+k) (sourceBlock3328PiPairs.getD k (0,0))
    (sourceEtaBatch3328Lower k, sourceEtaBatch3328Upper k)
    (sourceBlock3328TwoPairs.getD k (0,0))

theorem sourceBlock3328Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3328XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3328+k):ℂ)).re ∧
      (xi (xiGridArgument (3328+k):ℂ)).re ≤ ((sourceBlock3328XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3328+k) _ _ _
    (sourceBlock3328PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3328_actual_enclosure k hk)
    (sourceBlock3328TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3328Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3328XiPair k).1 := by
  decide +kernel

theorem sourceBlock3328Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3328Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3328XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3328XiPair k)).2 ≤
      sourceBlock3328Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3328_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3328+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3328+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3328Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3328+k) (sourceBlock3328XiPair k) _
    (sourceBlock3328Xi_enclosure k hk) (sourceBlock3328Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3328Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3360_bound (k : ℕ) (hk : k < 3360) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3328
  · exact sourceRoundedMidpoint_first3328_bound k h
  · have hsum : 3328+(k-3328) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3328_bound (k-3328) (by omega)

end ReciprocalXi
