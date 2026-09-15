import ProofWorkspace.Final.SourceBlock1984Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2016DataFull
import ProofWorkspace.Final.EtaBlock2016Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2016XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2016+k) (sourceBlock2016PiPairs.getD k (0,0))
    (sourceEtaBatch2016Lower k, sourceEtaBatch2016Upper k)
    (sourceBlock2016TwoPairs.getD k (0,0))

theorem sourceBlock2016Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2016XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2016+k):ℂ)).re ∧
      (xi (xiGridArgument (2016+k):ℂ)).re ≤ ((sourceBlock2016XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2016+k) _ _ _
    (sourceBlock2016PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2016_actual_enclosure k hk)
    (sourceBlock2016TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2016Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2016XiPair k).1 := by
  decide +kernel

theorem sourceBlock2016Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2016Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2016XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2016XiPair k)).2 ≤
      sourceBlock2016Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2016_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2016+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2016+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2016Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2016+k) (sourceBlock2016XiPair k) _
    (sourceBlock2016Xi_enclosure k hk) (sourceBlock2016Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2016Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2048_bound (k : ℕ) (hk : k < 2048) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2016
  · exact sourceRoundedMidpoint_first2016_bound k h
  · have hsum : 2016+(k-2016) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2016_bound (k-2016) (by omega)

end ReciprocalXi
