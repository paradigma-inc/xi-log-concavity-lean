import ProofWorkspace.Final.SourceBlock7136Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7168DataFull
import ProofWorkspace.Final.EtaBlock7168Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7168XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7168+k) (sourceBlock7168PiPairs.getD k (0,0))
    (sourceEtaBatch7168Lower k, sourceEtaBatch7168Upper k)
    (sourceBlock7168TwoPairs.getD k (0,0))

theorem sourceBlock7168Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7168XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7168+k):ℂ)).re ∧
      (xi (xiGridArgument (7168+k):ℂ)).re ≤ ((sourceBlock7168XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7168+k) _ _ _
    (sourceBlock7168PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7168_actual_enclosure k hk)
    (sourceBlock7168TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7168Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7168XiPair k).1 := by
  decide +kernel

theorem sourceBlock7168Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7168Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7168XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7168XiPair k)).2 ≤
      sourceBlock7168Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7168_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7168+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7168+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7168Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7168+k) (sourceBlock7168XiPair k) _
    (sourceBlock7168Xi_enclosure k hk) (sourceBlock7168Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7168Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7200_bound (k : ℕ) (hk : k < 7200) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7168
  · exact sourceRoundedMidpoint_first7168_bound k h
  · have hsum : 7168+(k-7168) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7168_bound (k-7168) (by omega)

end ReciprocalXi
