import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock160DataFull
import ProofWorkspace.Final.EtaBlock160Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock160XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (160+k) (sourceBlock160PiPairs.getD k (0,0))
    (sourceEtaBatch160Lower k, sourceEtaBatch160Upper k)
    (sourceBlock160TwoPairs.getD k (0,0))

theorem sourceBlock160Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock160XiPair k).1:ℝ) ≤ (xi (xiGridArgument (160+k):ℂ)).re ∧
      (xi (xiGridArgument (160+k):ℂ)).re ≤ ((sourceBlock160XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (160+k) _ _ _
    (sourceBlock160PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch160_actual_enclosure k hk)
    (sourceBlock160TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock160Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock160XiPair k).1 := by
  decide +kernel

theorem sourceBlock160Reciprocal_check : ∀ k : Fin 32,
    sourceBlock160Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock160XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock160XiPair k)).2 ≤
      sourceBlock160Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block160_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((160+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (160+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock160Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (160+k) (sourceBlock160XiPair k) _
    (sourceBlock160Xi_enclosure k hk) (sourceBlock160Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock160Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first192_bound (k : ℕ) (hk : k < 192) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 160
  · exact sourceRoundedMidpoint_first160_bound k h
  · have hsum : 160+(k-160) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block160_bound (k-160) (by omega)

end ReciprocalXi
