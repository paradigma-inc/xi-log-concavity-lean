import ProofWorkspace.Final.SourceBlock5536Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5568DataFull
import ProofWorkspace.Final.EtaBlock5568Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5568XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5568+k) (sourceBlock5568PiPairs.getD k (0,0))
    (sourceEtaBatch5568Lower k, sourceEtaBatch5568Upper k)
    (sourceBlock5568TwoPairs.getD k (0,0))

theorem sourceBlock5568Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5568XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5568+k):ℂ)).re ∧
      (xi (xiGridArgument (5568+k):ℂ)).re ≤ ((sourceBlock5568XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5568+k) _ _ _
    (sourceBlock5568PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5568_actual_enclosure k hk)
    (sourceBlock5568TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5568Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5568XiPair k).1 := by
  decide +kernel

theorem sourceBlock5568Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5568Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5568XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5568XiPair k)).2 ≤
      sourceBlock5568Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5568_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5568+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5568+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5568Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5568+k) (sourceBlock5568XiPair k) _
    (sourceBlock5568Xi_enclosure k hk) (sourceBlock5568Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5568Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5600_bound (k : ℕ) (hk : k < 5600) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5568
  · exact sourceRoundedMidpoint_first5568_bound k h
  · have hsum : 5568+(k-5568) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5568_bound (k-5568) (by omega)

end ReciprocalXi
