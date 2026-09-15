import ProofWorkspace.Final.SourceBlock3424Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3456DataFull
import ProofWorkspace.Final.EtaBlock3456Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3456XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3456+k) (sourceBlock3456PiPairs.getD k (0,0))
    (sourceEtaBatch3456Lower k, sourceEtaBatch3456Upper k)
    (sourceBlock3456TwoPairs.getD k (0,0))

theorem sourceBlock3456Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3456XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3456+k):ℂ)).re ∧
      (xi (xiGridArgument (3456+k):ℂ)).re ≤ ((sourceBlock3456XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3456+k) _ _ _
    (sourceBlock3456PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3456_actual_enclosure k hk)
    (sourceBlock3456TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3456Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3456XiPair k).1 := by
  decide +kernel

theorem sourceBlock3456Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3456Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3456XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3456XiPair k)).2 ≤
      sourceBlock3456Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3456_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3456+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3456+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3456Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3456+k) (sourceBlock3456XiPair k) _
    (sourceBlock3456Xi_enclosure k hk) (sourceBlock3456Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3456Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3488_bound (k : ℕ) (hk : k < 3488) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3456
  · exact sourceRoundedMidpoint_first3456_bound k h
  · have hsum : 3456+(k-3456) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3456_bound (k-3456) (by omega)

end ReciprocalXi
