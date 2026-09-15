import ProofWorkspace.Final.SourceBlock2080Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2112DataFull
import ProofWorkspace.Final.EtaBlock2112Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2112XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2112+k) (sourceBlock2112PiPairs.getD k (0,0))
    (sourceEtaBatch2112Lower k, sourceEtaBatch2112Upper k)
    (sourceBlock2112TwoPairs.getD k (0,0))

theorem sourceBlock2112Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2112XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2112+k):ℂ)).re ∧
      (xi (xiGridArgument (2112+k):ℂ)).re ≤ ((sourceBlock2112XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2112+k) _ _ _
    (sourceBlock2112PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2112_actual_enclosure k hk)
    (sourceBlock2112TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2112Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2112XiPair k).1 := by
  decide +kernel

theorem sourceBlock2112Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2112Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2112XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2112XiPair k)).2 ≤
      sourceBlock2112Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2112_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2112+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2112+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2112Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2112+k) (sourceBlock2112XiPair k) _
    (sourceBlock2112Xi_enclosure k hk) (sourceBlock2112Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2112Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2144_bound (k : ℕ) (hk : k < 2144) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2112
  · exact sourceRoundedMidpoint_first2112_bound k h
  · have hsum : 2112+(k-2112) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2112_bound (k-2112) (by omega)

end ReciprocalXi
