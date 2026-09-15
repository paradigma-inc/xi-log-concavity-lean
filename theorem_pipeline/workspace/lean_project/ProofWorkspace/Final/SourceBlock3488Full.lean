import ProofWorkspace.Final.SourceBlock3456Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3488DataFull
import ProofWorkspace.Final.EtaBlock3488Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3488XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3488+k) (sourceBlock3488PiPairs.getD k (0,0))
    (sourceEtaBatch3488Lower k, sourceEtaBatch3488Upper k)
    (sourceBlock3488TwoPairs.getD k (0,0))

theorem sourceBlock3488Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3488XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3488+k):ℂ)).re ∧
      (xi (xiGridArgument (3488+k):ℂ)).re ≤ ((sourceBlock3488XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3488+k) _ _ _
    (sourceBlock3488PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3488_actual_enclosure k hk)
    (sourceBlock3488TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3488Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3488XiPair k).1 := by
  decide +kernel

theorem sourceBlock3488Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3488Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3488XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3488XiPair k)).2 ≤
      sourceBlock3488Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3488_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3488+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3488+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3488Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3488+k) (sourceBlock3488XiPair k) _
    (sourceBlock3488Xi_enclosure k hk) (sourceBlock3488Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3488Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3520_bound (k : ℕ) (hk : k < 3520) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3488
  · exact sourceRoundedMidpoint_first3488_bound k h
  · have hsum : 3488+(k-3488) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3488_bound (k-3488) (by omega)

end ReciprocalXi
