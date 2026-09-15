import ProofWorkspace.Final.SourceBlock13376Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13408DataFull
import ProofWorkspace.Final.EtaBlock13408Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13408XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13408+k) (sourceBlock13408PiPairs.getD k (0,0))
    (sourceEtaBatch13408Lower k, sourceEtaBatch13408Upper k)
    (sourceBlock13408TwoPairs.getD k (0,0))

theorem sourceBlock13408Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13408XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13408+k):ℂ)).re ∧
      (xi (xiGridArgument (13408+k):ℂ)).re ≤ ((sourceBlock13408XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13408+k) _ _ _
    (sourceBlock13408PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13408_actual_enclosure k hk)
    (sourceBlock13408TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13408Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13408XiPair k).1 := by
  decide +kernel

theorem sourceBlock13408Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13408Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13408XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13408XiPair k)).2 ≤
      sourceBlock13408Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13408_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13408+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13408+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13408Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13408+k) (sourceBlock13408XiPair k) _
    (sourceBlock13408Xi_enclosure k hk) (sourceBlock13408Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13408Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13440_bound (k : ℕ) (hk : k < 13440) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13408
  · exact sourceRoundedMidpoint_first13408_bound k h
  · have hsum : 13408+(k-13408) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13408_bound (k-13408) (by omega)

end ReciprocalXi
