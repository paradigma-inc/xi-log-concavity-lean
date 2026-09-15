import ProofWorkspace.Final.SourceBlock12928Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12960DataFull
import ProofWorkspace.Final.EtaBlock12960Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12960XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12960+k) (sourceBlock12960PiPairs.getD k (0,0))
    (sourceEtaBatch12960Lower k, sourceEtaBatch12960Upper k)
    (sourceBlock12960TwoPairs.getD k (0,0))

theorem sourceBlock12960Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12960XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12960+k):ℂ)).re ∧
      (xi (xiGridArgument (12960+k):ℂ)).re ≤ ((sourceBlock12960XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12960+k) _ _ _
    (sourceBlock12960PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12960_actual_enclosure k hk)
    (sourceBlock12960TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12960Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12960XiPair k).1 := by
  decide +kernel

theorem sourceBlock12960Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12960Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12960XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12960XiPair k)).2 ≤
      sourceBlock12960Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12960_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12960+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12960+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12960Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12960+k) (sourceBlock12960XiPair k) _
    (sourceBlock12960Xi_enclosure k hk) (sourceBlock12960Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12960Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12992_bound (k : ℕ) (hk : k < 12992) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12960
  · exact sourceRoundedMidpoint_first12960_bound k h
  · have hsum : 12960+(k-12960) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12960_bound (k-12960) (by omega)

end ReciprocalXi
