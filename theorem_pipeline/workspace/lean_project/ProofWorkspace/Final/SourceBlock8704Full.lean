import ProofWorkspace.Final.SourceBlock8672Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8704DataFull
import ProofWorkspace.Final.EtaBlock8704Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8704XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8704+k) (sourceBlock8704PiPairs.getD k (0,0))
    (sourceEtaBatch8704Lower k, sourceEtaBatch8704Upper k)
    (sourceBlock8704TwoPairs.getD k (0,0))

theorem sourceBlock8704Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8704XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8704+k):ℂ)).re ∧
      (xi (xiGridArgument (8704+k):ℂ)).re ≤ ((sourceBlock8704XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8704+k) _ _ _
    (sourceBlock8704PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8704_actual_enclosure k hk)
    (sourceBlock8704TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8704Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8704XiPair k).1 := by
  decide +kernel

theorem sourceBlock8704Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8704Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8704XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8704XiPair k)).2 ≤
      sourceBlock8704Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8704_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8704+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8704+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8704Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8704+k) (sourceBlock8704XiPair k) _
    (sourceBlock8704Xi_enclosure k hk) (sourceBlock8704Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8704Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8736_bound (k : ℕ) (hk : k < 8736) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8704
  · exact sourceRoundedMidpoint_first8704_bound k h
  · have hsum : 8704+(k-8704) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8704_bound (k-8704) (by omega)

end ReciprocalXi
