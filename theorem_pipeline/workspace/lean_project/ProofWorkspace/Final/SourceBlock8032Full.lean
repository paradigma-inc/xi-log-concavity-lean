import ProofWorkspace.Final.SourceBlock8000Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8032DataFull
import ProofWorkspace.Final.EtaBlock8032Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8032XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8032+k) (sourceBlock8032PiPairs.getD k (0,0))
    (sourceEtaBatch8032Lower k, sourceEtaBatch8032Upper k)
    (sourceBlock8032TwoPairs.getD k (0,0))

theorem sourceBlock8032Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8032XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8032+k):ℂ)).re ∧
      (xi (xiGridArgument (8032+k):ℂ)).re ≤ ((sourceBlock8032XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8032+k) _ _ _
    (sourceBlock8032PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8032_actual_enclosure k hk)
    (sourceBlock8032TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8032Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8032XiPair k).1 := by
  decide +kernel

theorem sourceBlock8032Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8032Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8032XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8032XiPair k)).2 ≤
      sourceBlock8032Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8032_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8032+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8032+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8032Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8032+k) (sourceBlock8032XiPair k) _
    (sourceBlock8032Xi_enclosure k hk) (sourceBlock8032Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8032Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8064_bound (k : ℕ) (hk : k < 8064) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8032
  · exact sourceRoundedMidpoint_first8032_bound k h
  · have hsum : 8032+(k-8032) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8032_bound (k-8032) (by omega)

end ReciprocalXi
