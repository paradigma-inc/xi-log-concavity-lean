import ProofWorkspace.Final.SourceBlock6080Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6112DataFull
import ProofWorkspace.Final.EtaBlock6112Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6112XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6112+k) (sourceBlock6112PiPairs.getD k (0,0))
    (sourceEtaBatch6112Lower k, sourceEtaBatch6112Upper k)
    (sourceBlock6112TwoPairs.getD k (0,0))

theorem sourceBlock6112Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6112XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6112+k):ℂ)).re ∧
      (xi (xiGridArgument (6112+k):ℂ)).re ≤ ((sourceBlock6112XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6112+k) _ _ _
    (sourceBlock6112PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6112_actual_enclosure k hk)
    (sourceBlock6112TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6112Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6112XiPair k).1 := by
  decide +kernel

theorem sourceBlock6112Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6112Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6112XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6112XiPair k)).2 ≤
      sourceBlock6112Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6112_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6112+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6112+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6112Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6112+k) (sourceBlock6112XiPair k) _
    (sourceBlock6112Xi_enclosure k hk) (sourceBlock6112Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6112Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6144_bound (k : ℕ) (hk : k < 6144) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6112
  · exact sourceRoundedMidpoint_first6112_bound k h
  · have hsum : 6112+(k-6112) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6112_bound (k-6112) (by omega)

end ReciprocalXi
