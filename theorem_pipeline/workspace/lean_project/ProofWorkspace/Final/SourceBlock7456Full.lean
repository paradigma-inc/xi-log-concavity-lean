import ProofWorkspace.Final.SourceBlock7424Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7456DataFull
import ProofWorkspace.Final.EtaBlock7456Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7456XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7456+k) (sourceBlock7456PiPairs.getD k (0,0))
    (sourceEtaBatch7456Lower k, sourceEtaBatch7456Upper k)
    (sourceBlock7456TwoPairs.getD k (0,0))

theorem sourceBlock7456Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7456XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7456+k):ℂ)).re ∧
      (xi (xiGridArgument (7456+k):ℂ)).re ≤ ((sourceBlock7456XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7456+k) _ _ _
    (sourceBlock7456PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7456_actual_enclosure k hk)
    (sourceBlock7456TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7456Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7456XiPair k).1 := by
  decide +kernel

theorem sourceBlock7456Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7456Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7456XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7456XiPair k)).2 ≤
      sourceBlock7456Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7456_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7456+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7456+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7456Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7456+k) (sourceBlock7456XiPair k) _
    (sourceBlock7456Xi_enclosure k hk) (sourceBlock7456Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7456Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7488_bound (k : ℕ) (hk : k < 7488) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7456
  · exact sourceRoundedMidpoint_first7456_bound k h
  · have hsum : 7456+(k-7456) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7456_bound (k-7456) (by omega)

end ReciprocalXi
