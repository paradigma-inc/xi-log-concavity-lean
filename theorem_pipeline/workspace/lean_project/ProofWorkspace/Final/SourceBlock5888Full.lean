import ProofWorkspace.Final.SourceBlock5856Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5888DataFull
import ProofWorkspace.Final.EtaBlock5888Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5888XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5888+k) (sourceBlock5888PiPairs.getD k (0,0))
    (sourceEtaBatch5888Lower k, sourceEtaBatch5888Upper k)
    (sourceBlock5888TwoPairs.getD k (0,0))

theorem sourceBlock5888Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5888XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5888+k):ℂ)).re ∧
      (xi (xiGridArgument (5888+k):ℂ)).re ≤ ((sourceBlock5888XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5888+k) _ _ _
    (sourceBlock5888PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5888_actual_enclosure k hk)
    (sourceBlock5888TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5888Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5888XiPair k).1 := by
  decide +kernel

theorem sourceBlock5888Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5888Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5888XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5888XiPair k)).2 ≤
      sourceBlock5888Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5888_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5888+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5888+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5888Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5888+k) (sourceBlock5888XiPair k) _
    (sourceBlock5888Xi_enclosure k hk) (sourceBlock5888Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5888Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5920_bound (k : ℕ) (hk : k < 5920) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5888
  · exact sourceRoundedMidpoint_first5888_bound k h
  · have hsum : 5888+(k-5888) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5888_bound (k-5888) (by omega)

end ReciprocalXi
