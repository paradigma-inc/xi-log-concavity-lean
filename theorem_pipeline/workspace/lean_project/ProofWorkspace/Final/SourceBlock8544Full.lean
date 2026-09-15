import ProofWorkspace.Final.SourceBlock8512Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8544DataFull
import ProofWorkspace.Final.EtaBlock8544Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8544XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8544+k) (sourceBlock8544PiPairs.getD k (0,0))
    (sourceEtaBatch8544Lower k, sourceEtaBatch8544Upper k)
    (sourceBlock8544TwoPairs.getD k (0,0))

theorem sourceBlock8544Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8544XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8544+k):ℂ)).re ∧
      (xi (xiGridArgument (8544+k):ℂ)).re ≤ ((sourceBlock8544XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8544+k) _ _ _
    (sourceBlock8544PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8544_actual_enclosure k hk)
    (sourceBlock8544TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8544Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8544XiPair k).1 := by
  decide +kernel

theorem sourceBlock8544Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8544Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8544XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8544XiPair k)).2 ≤
      sourceBlock8544Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8544_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8544+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8544+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8544Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8544+k) (sourceBlock8544XiPair k) _
    (sourceBlock8544Xi_enclosure k hk) (sourceBlock8544Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8544Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8576_bound (k : ℕ) (hk : k < 8576) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8544
  · exact sourceRoundedMidpoint_first8544_bound k h
  · have hsum : 8544+(k-8544) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8544_bound (k-8544) (by omega)

end ReciprocalXi
