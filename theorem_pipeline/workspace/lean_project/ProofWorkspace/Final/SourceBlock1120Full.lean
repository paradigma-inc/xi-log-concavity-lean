import ProofWorkspace.Final.SourceBlock1088Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1120DataFull
import ProofWorkspace.Final.EtaBlock1120Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1120XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1120+k) (sourceBlock1120PiPairs.getD k (0,0))
    (sourceEtaBatch1120Lower k, sourceEtaBatch1120Upper k)
    (sourceBlock1120TwoPairs.getD k (0,0))

theorem sourceBlock1120Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1120XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1120+k):ℂ)).re ∧
      (xi (xiGridArgument (1120+k):ℂ)).re ≤ ((sourceBlock1120XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1120+k) _ _ _
    (sourceBlock1120PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1120_actual_enclosure k hk)
    (sourceBlock1120TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1120Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1120XiPair k).1 := by
  decide +kernel

theorem sourceBlock1120Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1120Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1120XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1120XiPair k)).2 ≤
      sourceBlock1120Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1120_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1120+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1120+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1120Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1120+k) (sourceBlock1120XiPair k) _
    (sourceBlock1120Xi_enclosure k hk) (sourceBlock1120Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1120Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1152_bound (k : ℕ) (hk : k < 1152) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1120
  · exact sourceRoundedMidpoint_first1120_bound k h
  · have hsum : 1120+(k-1120) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1120_bound (k-1120) (by omega)

end ReciprocalXi
