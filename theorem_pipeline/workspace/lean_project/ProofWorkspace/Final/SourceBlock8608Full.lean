import ProofWorkspace.Final.SourceBlock8576Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8608DataFull
import ProofWorkspace.Final.EtaBlock8608Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8608XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8608+k) (sourceBlock8608PiPairs.getD k (0,0))
    (sourceEtaBatch8608Lower k, sourceEtaBatch8608Upper k)
    (sourceBlock8608TwoPairs.getD k (0,0))

theorem sourceBlock8608Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8608XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8608+k):ℂ)).re ∧
      (xi (xiGridArgument (8608+k):ℂ)).re ≤ ((sourceBlock8608XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8608+k) _ _ _
    (sourceBlock8608PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8608_actual_enclosure k hk)
    (sourceBlock8608TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8608Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8608XiPair k).1 := by
  decide +kernel

theorem sourceBlock8608Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8608Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8608XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8608XiPair k)).2 ≤
      sourceBlock8608Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8608_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8608+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8608+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8608Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8608+k) (sourceBlock8608XiPair k) _
    (sourceBlock8608Xi_enclosure k hk) (sourceBlock8608Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8608Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8640_bound (k : ℕ) (hk : k < 8640) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8608
  · exact sourceRoundedMidpoint_first8608_bound k h
  · have hsum : 8608+(k-8608) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8608_bound (k-8608) (by omega)

end ReciprocalXi
