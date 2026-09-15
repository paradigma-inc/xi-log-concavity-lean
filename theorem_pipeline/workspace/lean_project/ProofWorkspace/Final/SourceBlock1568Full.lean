import ProofWorkspace.Final.SourceBlock1536Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1568DataFull
import ProofWorkspace.Final.EtaBlock1568Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1568XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1568+k) (sourceBlock1568PiPairs.getD k (0,0))
    (sourceEtaBatch1568Lower k, sourceEtaBatch1568Upper k)
    (sourceBlock1568TwoPairs.getD k (0,0))

theorem sourceBlock1568Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1568XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1568+k):ℂ)).re ∧
      (xi (xiGridArgument (1568+k):ℂ)).re ≤ ((sourceBlock1568XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1568+k) _ _ _
    (sourceBlock1568PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1568_actual_enclosure k hk)
    (sourceBlock1568TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1568Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1568XiPair k).1 := by
  decide +kernel

theorem sourceBlock1568Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1568Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1568XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1568XiPair k)).2 ≤
      sourceBlock1568Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1568_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1568+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1568+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1568Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1568+k) (sourceBlock1568XiPair k) _
    (sourceBlock1568Xi_enclosure k hk) (sourceBlock1568Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1568Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1600_bound (k : ℕ) (hk : k < 1600) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1568
  · exact sourceRoundedMidpoint_first1568_bound k h
  · have hsum : 1568+(k-1568) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1568_bound (k-1568) (by omega)

end ReciprocalXi
