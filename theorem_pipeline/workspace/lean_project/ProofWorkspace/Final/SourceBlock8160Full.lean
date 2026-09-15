import ProofWorkspace.Final.SourceBlock8128Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8160DataFull
import ProofWorkspace.Final.EtaBlock8160Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8160XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8160+k) (sourceBlock8160PiPairs.getD k (0,0))
    (sourceEtaBatch8160Lower k, sourceEtaBatch8160Upper k)
    (sourceBlock8160TwoPairs.getD k (0,0))

theorem sourceBlock8160Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8160XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8160+k):ℂ)).re ∧
      (xi (xiGridArgument (8160+k):ℂ)).re ≤ ((sourceBlock8160XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8160+k) _ _ _
    (sourceBlock8160PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8160_actual_enclosure k hk)
    (sourceBlock8160TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8160Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8160XiPair k).1 := by
  decide +kernel

theorem sourceBlock8160Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8160Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8160XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8160XiPair k)).2 ≤
      sourceBlock8160Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8160_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8160+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8160+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8160Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8160+k) (sourceBlock8160XiPair k) _
    (sourceBlock8160Xi_enclosure k hk) (sourceBlock8160Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8160Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8192_bound (k : ℕ) (hk : k < 8192) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8160
  · exact sourceRoundedMidpoint_first8160_bound k h
  · have hsum : 8160+(k-8160) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8160_bound (k-8160) (by omega)

end ReciprocalXi
