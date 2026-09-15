import ProofWorkspace.Final.SourceBlock2304Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2336DataFull
import ProofWorkspace.Final.EtaBlock2336Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2336XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2336+k) (sourceBlock2336PiPairs.getD k (0,0))
    (sourceEtaBatch2336Lower k, sourceEtaBatch2336Upper k)
    (sourceBlock2336TwoPairs.getD k (0,0))

theorem sourceBlock2336Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2336XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2336+k):ℂ)).re ∧
      (xi (xiGridArgument (2336+k):ℂ)).re ≤ ((sourceBlock2336XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2336+k) _ _ _
    (sourceBlock2336PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2336_actual_enclosure k hk)
    (sourceBlock2336TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2336Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2336XiPair k).1 := by
  decide +kernel

theorem sourceBlock2336Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2336Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2336XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2336XiPair k)).2 ≤
      sourceBlock2336Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2336_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2336+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2336+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2336Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2336+k) (sourceBlock2336XiPair k) _
    (sourceBlock2336Xi_enclosure k hk) (sourceBlock2336Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2336Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2368_bound (k : ℕ) (hk : k < 2368) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2336
  · exact sourceRoundedMidpoint_first2336_bound k h
  · have hsum : 2336+(k-2336) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2336_bound (k-2336) (by omega)

end ReciprocalXi
