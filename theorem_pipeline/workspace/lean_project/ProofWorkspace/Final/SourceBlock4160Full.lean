import ProofWorkspace.Final.SourceBlock4128Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4160DataFull
import ProofWorkspace.Final.EtaBlock4160Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4160XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4160+k) (sourceBlock4160PiPairs.getD k (0,0))
    (sourceEtaBatch4160Lower k, sourceEtaBatch4160Upper k)
    (sourceBlock4160TwoPairs.getD k (0,0))

theorem sourceBlock4160Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4160XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4160+k):ℂ)).re ∧
      (xi (xiGridArgument (4160+k):ℂ)).re ≤ ((sourceBlock4160XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4160+k) _ _ _
    (sourceBlock4160PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4160_actual_enclosure k hk)
    (sourceBlock4160TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4160Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4160XiPair k).1 := by
  decide +kernel

theorem sourceBlock4160Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4160Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4160XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4160XiPair k)).2 ≤
      sourceBlock4160Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4160_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4160+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4160+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4160Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4160+k) (sourceBlock4160XiPair k) _
    (sourceBlock4160Xi_enclosure k hk) (sourceBlock4160Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4160Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4192_bound (k : ℕ) (hk : k < 4192) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4160
  · exact sourceRoundedMidpoint_first4160_bound k h
  · have hsum : 4160+(k-4160) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4160_bound (k-4160) (by omega)

end ReciprocalXi
