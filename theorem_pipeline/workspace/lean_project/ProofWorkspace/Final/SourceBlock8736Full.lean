import ProofWorkspace.Final.SourceBlock8704Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8736DataFull
import ProofWorkspace.Final.EtaBlock8736Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8736XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8736+k) (sourceBlock8736PiPairs.getD k (0,0))
    (sourceEtaBatch8736Lower k, sourceEtaBatch8736Upper k)
    (sourceBlock8736TwoPairs.getD k (0,0))

theorem sourceBlock8736Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8736XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8736+k):ℂ)).re ∧
      (xi (xiGridArgument (8736+k):ℂ)).re ≤ ((sourceBlock8736XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8736+k) _ _ _
    (sourceBlock8736PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8736_actual_enclosure k hk)
    (sourceBlock8736TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8736Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8736XiPair k).1 := by
  decide +kernel

theorem sourceBlock8736Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8736Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8736XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8736XiPair k)).2 ≤
      sourceBlock8736Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8736_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8736+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8736+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8736Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8736+k) (sourceBlock8736XiPair k) _
    (sourceBlock8736Xi_enclosure k hk) (sourceBlock8736Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8736Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8768_bound (k : ℕ) (hk : k < 8768) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8736
  · exact sourceRoundedMidpoint_first8736_bound k h
  · have hsum : 8736+(k-8736) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8736_bound (k-8736) (by omega)

end ReciprocalXi
