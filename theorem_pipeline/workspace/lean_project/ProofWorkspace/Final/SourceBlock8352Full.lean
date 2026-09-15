import ProofWorkspace.Final.SourceBlock8320Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8352DataFull
import ProofWorkspace.Final.EtaBlock8352Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8352XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8352+k) (sourceBlock8352PiPairs.getD k (0,0))
    (sourceEtaBatch8352Lower k, sourceEtaBatch8352Upper k)
    (sourceBlock8352TwoPairs.getD k (0,0))

theorem sourceBlock8352Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8352XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8352+k):ℂ)).re ∧
      (xi (xiGridArgument (8352+k):ℂ)).re ≤ ((sourceBlock8352XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8352+k) _ _ _
    (sourceBlock8352PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8352_actual_enclosure k hk)
    (sourceBlock8352TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8352Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8352XiPair k).1 := by
  decide +kernel

theorem sourceBlock8352Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8352Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8352XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8352XiPair k)).2 ≤
      sourceBlock8352Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8352_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8352+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8352+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8352Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8352+k) (sourceBlock8352XiPair k) _
    (sourceBlock8352Xi_enclosure k hk) (sourceBlock8352Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8352Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8384_bound (k : ℕ) (hk : k < 8384) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8352
  · exact sourceRoundedMidpoint_first8352_bound k h
  · have hsum : 8352+(k-8352) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8352_bound (k-8352) (by omega)

end ReciprocalXi
