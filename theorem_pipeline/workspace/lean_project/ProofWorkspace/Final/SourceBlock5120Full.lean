import ProofWorkspace.Final.SourceBlock5088Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5120DataFull
import ProofWorkspace.Final.EtaBlock5120Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5120XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5120+k) (sourceBlock5120PiPairs.getD k (0,0))
    (sourceEtaBatch5120Lower k, sourceEtaBatch5120Upper k)
    (sourceBlock5120TwoPairs.getD k (0,0))

theorem sourceBlock5120Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5120XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5120+k):ℂ)).re ∧
      (xi (xiGridArgument (5120+k):ℂ)).re ≤ ((sourceBlock5120XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5120+k) _ _ _
    (sourceBlock5120PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5120_actual_enclosure k hk)
    (sourceBlock5120TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5120Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5120XiPair k).1 := by
  decide +kernel

theorem sourceBlock5120Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5120Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5120XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5120XiPair k)).2 ≤
      sourceBlock5120Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5120_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5120+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5120+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5120Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5120+k) (sourceBlock5120XiPair k) _
    (sourceBlock5120Xi_enclosure k hk) (sourceBlock5120Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5120Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5152_bound (k : ℕ) (hk : k < 5152) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5120
  · exact sourceRoundedMidpoint_first5120_bound k h
  · have hsum : 5120+(k-5120) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5120_bound (k-5120) (by omega)

end ReciprocalXi
