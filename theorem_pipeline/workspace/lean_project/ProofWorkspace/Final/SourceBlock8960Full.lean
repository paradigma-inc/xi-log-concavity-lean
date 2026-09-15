import ProofWorkspace.Final.SourceBlock8928Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8960DataFull
import ProofWorkspace.Final.EtaBlock8960Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8960XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8960+k) (sourceBlock8960PiPairs.getD k (0,0))
    (sourceEtaBatch8960Lower k, sourceEtaBatch8960Upper k)
    (sourceBlock8960TwoPairs.getD k (0,0))

theorem sourceBlock8960Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8960XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8960+k):ℂ)).re ∧
      (xi (xiGridArgument (8960+k):ℂ)).re ≤ ((sourceBlock8960XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8960+k) _ _ _
    (sourceBlock8960PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8960_actual_enclosure k hk)
    (sourceBlock8960TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8960Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8960XiPair k).1 := by
  decide +kernel

theorem sourceBlock8960Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8960Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8960XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8960XiPair k)).2 ≤
      sourceBlock8960Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8960_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8960+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8960+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8960Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8960+k) (sourceBlock8960XiPair k) _
    (sourceBlock8960Xi_enclosure k hk) (sourceBlock8960Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8960Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8992_bound (k : ℕ) (hk : k < 8992) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8960
  · exact sourceRoundedMidpoint_first8960_bound k h
  · have hsum : 8960+(k-8960) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8960_bound (k-8960) (by omega)

end ReciprocalXi
