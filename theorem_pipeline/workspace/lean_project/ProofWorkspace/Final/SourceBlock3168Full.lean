import ProofWorkspace.Final.SourceBlock3136Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3168DataFull
import ProofWorkspace.Final.EtaBlock3168Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3168XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3168+k) (sourceBlock3168PiPairs.getD k (0,0))
    (sourceEtaBatch3168Lower k, sourceEtaBatch3168Upper k)
    (sourceBlock3168TwoPairs.getD k (0,0))

theorem sourceBlock3168Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3168XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3168+k):ℂ)).re ∧
      (xi (xiGridArgument (3168+k):ℂ)).re ≤ ((sourceBlock3168XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3168+k) _ _ _
    (sourceBlock3168PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3168_actual_enclosure k hk)
    (sourceBlock3168TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3168Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3168XiPair k).1 := by
  decide +kernel

theorem sourceBlock3168Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3168Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3168XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3168XiPair k)).2 ≤
      sourceBlock3168Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3168_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3168+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3168+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3168Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3168+k) (sourceBlock3168XiPair k) _
    (sourceBlock3168Xi_enclosure k hk) (sourceBlock3168Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3168Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3200_bound (k : ℕ) (hk : k < 3200) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3168
  · exact sourceRoundedMidpoint_first3168_bound k h
  · have hsum : 3168+(k-3168) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3168_bound (k-3168) (by omega)

end ReciprocalXi
