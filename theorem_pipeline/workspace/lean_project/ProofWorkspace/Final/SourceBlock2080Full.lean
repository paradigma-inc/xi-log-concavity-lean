import ProofWorkspace.Final.SourceBlock2048Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2080DataFull
import ProofWorkspace.Final.EtaBlock2080Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2080XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2080+k) (sourceBlock2080PiPairs.getD k (0,0))
    (sourceEtaBatch2080Lower k, sourceEtaBatch2080Upper k)
    (sourceBlock2080TwoPairs.getD k (0,0))

theorem sourceBlock2080Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2080XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2080+k):ℂ)).re ∧
      (xi (xiGridArgument (2080+k):ℂ)).re ≤ ((sourceBlock2080XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2080+k) _ _ _
    (sourceBlock2080PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2080_actual_enclosure k hk)
    (sourceBlock2080TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2080Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2080XiPair k).1 := by
  decide +kernel

theorem sourceBlock2080Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2080Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2080XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2080XiPair k)).2 ≤
      sourceBlock2080Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2080_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2080+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2080+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2080Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2080+k) (sourceBlock2080XiPair k) _
    (sourceBlock2080Xi_enclosure k hk) (sourceBlock2080Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2080Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2112_bound (k : ℕ) (hk : k < 2112) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2080
  · exact sourceRoundedMidpoint_first2080_bound k h
  · have hsum : 2080+(k-2080) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2080_bound (k-2080) (by omega)

end ReciprocalXi
