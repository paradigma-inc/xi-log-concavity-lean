import ProofWorkspace.Final.SourceBlock1856Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1888DataFull
import ProofWorkspace.Final.EtaBlock1888Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1888XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1888+k) (sourceBlock1888PiPairs.getD k (0,0))
    (sourceEtaBatch1888Lower k, sourceEtaBatch1888Upper k)
    (sourceBlock1888TwoPairs.getD k (0,0))

theorem sourceBlock1888Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1888XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1888+k):ℂ)).re ∧
      (xi (xiGridArgument (1888+k):ℂ)).re ≤ ((sourceBlock1888XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1888+k) _ _ _
    (sourceBlock1888PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1888_actual_enclosure k hk)
    (sourceBlock1888TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1888Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1888XiPair k).1 := by
  decide +kernel

theorem sourceBlock1888Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1888Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1888XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1888XiPair k)).2 ≤
      sourceBlock1888Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1888_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1888+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1888+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1888Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1888+k) (sourceBlock1888XiPair k) _
    (sourceBlock1888Xi_enclosure k hk) (sourceBlock1888Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1888Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1920_bound (k : ℕ) (hk : k < 1920) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1888
  · exact sourceRoundedMidpoint_first1888_bound k h
  · have hsum : 1888+(k-1888) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1888_bound (k-1888) (by omega)

end ReciprocalXi
