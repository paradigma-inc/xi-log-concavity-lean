import ProofWorkspace.Final.SourceBlock13536Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13568DataFull
import ProofWorkspace.Final.EtaBlock13568Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13568XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13568+k) (sourceBlock13568PiPairs.getD k (0,0))
    (sourceEtaBatch13568Lower k, sourceEtaBatch13568Upper k)
    (sourceBlock13568TwoPairs.getD k (0,0))

theorem sourceBlock13568Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13568XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13568+k):ℂ)).re ∧
      (xi (xiGridArgument (13568+k):ℂ)).re ≤ ((sourceBlock13568XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13568+k) _ _ _
    (sourceBlock13568PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13568_actual_enclosure k hk)
    (sourceBlock13568TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13568Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13568XiPair k).1 := by
  decide +kernel

theorem sourceBlock13568Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13568Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13568XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13568XiPair k)).2 ≤
      sourceBlock13568Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13568_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13568+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13568+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13568Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13568+k) (sourceBlock13568XiPair k) _
    (sourceBlock13568Xi_enclosure k hk) (sourceBlock13568Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13568Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13600_bound (k : ℕ) (hk : k < 13600) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13568
  · exact sourceRoundedMidpoint_first13568_bound k h
  · have hsum : 13568+(k-13568) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13568_bound (k-13568) (by omega)

end ReciprocalXi
