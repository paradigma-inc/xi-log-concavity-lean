import ProofWorkspace.Final.SourceBlock4928Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4960DataFull
import ProofWorkspace.Final.EtaBlock4960Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4960XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4960+k) (sourceBlock4960PiPairs.getD k (0,0))
    (sourceEtaBatch4960Lower k, sourceEtaBatch4960Upper k)
    (sourceBlock4960TwoPairs.getD k (0,0))

theorem sourceBlock4960Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4960XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4960+k):ℂ)).re ∧
      (xi (xiGridArgument (4960+k):ℂ)).re ≤ ((sourceBlock4960XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4960+k) _ _ _
    (sourceBlock4960PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4960_actual_enclosure k hk)
    (sourceBlock4960TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4960Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4960XiPair k).1 := by
  decide +kernel

theorem sourceBlock4960Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4960Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4960XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4960XiPair k)).2 ≤
      sourceBlock4960Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4960_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4960+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4960+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4960Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4960+k) (sourceBlock4960XiPair k) _
    (sourceBlock4960Xi_enclosure k hk) (sourceBlock4960Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4960Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4992_bound (k : ℕ) (hk : k < 4992) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4960
  · exact sourceRoundedMidpoint_first4960_bound k h
  · have hsum : 4960+(k-4960) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4960_bound (k-4960) (by omega)

end ReciprocalXi
