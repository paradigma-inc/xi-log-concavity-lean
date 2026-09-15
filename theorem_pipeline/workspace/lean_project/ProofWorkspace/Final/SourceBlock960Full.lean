import ProofWorkspace.Final.SourceBlock928Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock960DataFull
import ProofWorkspace.Final.EtaBlock960Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock960XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (960+k) (sourceBlock960PiPairs.getD k (0,0))
    (sourceEtaBatch960Lower k, sourceEtaBatch960Upper k)
    (sourceBlock960TwoPairs.getD k (0,0))

theorem sourceBlock960Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock960XiPair k).1:ℝ) ≤ (xi (xiGridArgument (960+k):ℂ)).re ∧
      (xi (xiGridArgument (960+k):ℂ)).re ≤ ((sourceBlock960XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (960+k) _ _ _
    (sourceBlock960PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch960_actual_enclosure k hk)
    (sourceBlock960TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock960Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock960XiPair k).1 := by
  decide +kernel

theorem sourceBlock960Reciprocal_check : ∀ k : Fin 32,
    sourceBlock960Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock960XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock960XiPair k)).2 ≤
      sourceBlock960Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block960_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((960+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (960+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock960Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (960+k) (sourceBlock960XiPair k) _
    (sourceBlock960Xi_enclosure k hk) (sourceBlock960Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock960Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first992_bound (k : ℕ) (hk : k < 992) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 960
  · exact sourceRoundedMidpoint_first960_bound k h
  · have hsum : 960+(k-960) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block960_bound (k-960) (by omega)

end ReciprocalXi
