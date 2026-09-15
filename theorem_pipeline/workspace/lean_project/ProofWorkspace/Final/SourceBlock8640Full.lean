import ProofWorkspace.Final.SourceBlock8608Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8640DataFull
import ProofWorkspace.Final.EtaBlock8640Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8640XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8640+k) (sourceBlock8640PiPairs.getD k (0,0))
    (sourceEtaBatch8640Lower k, sourceEtaBatch8640Upper k)
    (sourceBlock8640TwoPairs.getD k (0,0))

theorem sourceBlock8640Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8640XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8640+k):ℂ)).re ∧
      (xi (xiGridArgument (8640+k):ℂ)).re ≤ ((sourceBlock8640XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8640+k) _ _ _
    (sourceBlock8640PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8640_actual_enclosure k hk)
    (sourceBlock8640TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8640Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8640XiPair k).1 := by
  decide +kernel

theorem sourceBlock8640Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8640Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8640XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8640XiPair k)).2 ≤
      sourceBlock8640Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8640_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8640+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8640+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8640Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8640+k) (sourceBlock8640XiPair k) _
    (sourceBlock8640Xi_enclosure k hk) (sourceBlock8640Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8640Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8672_bound (k : ℕ) (hk : k < 8672) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8640
  · exact sourceRoundedMidpoint_first8640_bound k h
  · have hsum : 8640+(k-8640) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8640_bound (k-8640) (by omega)

end ReciprocalXi
