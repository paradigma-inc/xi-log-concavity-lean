import ProofWorkspace.Final.SourceBlock8544Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8576DataFull
import ProofWorkspace.Final.EtaBlock8576Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8576XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8576+k) (sourceBlock8576PiPairs.getD k (0,0))
    (sourceEtaBatch8576Lower k, sourceEtaBatch8576Upper k)
    (sourceBlock8576TwoPairs.getD k (0,0))

theorem sourceBlock8576Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8576XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8576+k):ℂ)).re ∧
      (xi (xiGridArgument (8576+k):ℂ)).re ≤ ((sourceBlock8576XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8576+k) _ _ _
    (sourceBlock8576PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8576_actual_enclosure k hk)
    (sourceBlock8576TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8576Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8576XiPair k).1 := by
  decide +kernel

theorem sourceBlock8576Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8576Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8576XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8576XiPair k)).2 ≤
      sourceBlock8576Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8576_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8576+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8576+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8576Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8576+k) (sourceBlock8576XiPair k) _
    (sourceBlock8576Xi_enclosure k hk) (sourceBlock8576Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8576Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8608_bound (k : ℕ) (hk : k < 8608) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8576
  · exact sourceRoundedMidpoint_first8576_bound k h
  · have hsum : 8576+(k-8576) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8576_bound (k-8576) (by omega)

end ReciprocalXi
