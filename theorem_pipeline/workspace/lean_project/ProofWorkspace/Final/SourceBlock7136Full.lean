import ProofWorkspace.Final.SourceBlock7104Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7136DataFull
import ProofWorkspace.Final.EtaBlock7136Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7136XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7136+k) (sourceBlock7136PiPairs.getD k (0,0))
    (sourceEtaBatch7136Lower k, sourceEtaBatch7136Upper k)
    (sourceBlock7136TwoPairs.getD k (0,0))

theorem sourceBlock7136Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7136XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7136+k):ℂ)).re ∧
      (xi (xiGridArgument (7136+k):ℂ)).re ≤ ((sourceBlock7136XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7136+k) _ _ _
    (sourceBlock7136PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7136_actual_enclosure k hk)
    (sourceBlock7136TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7136Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7136XiPair k).1 := by
  decide +kernel

theorem sourceBlock7136Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7136Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7136XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7136XiPair k)).2 ≤
      sourceBlock7136Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7136_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7136+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7136+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7136Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7136+k) (sourceBlock7136XiPair k) _
    (sourceBlock7136Xi_enclosure k hk) (sourceBlock7136Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7136Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7168_bound (k : ℕ) (hk : k < 7168) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7136
  · exact sourceRoundedMidpoint_first7136_bound k h
  · have hsum : 7136+(k-7136) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7136_bound (k-7136) (by omega)

end ReciprocalXi
