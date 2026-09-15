import ProofWorkspace.Final.SourceBlock2272Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2304DataFull
import ProofWorkspace.Final.EtaBlock2304Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2304XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2304+k) (sourceBlock2304PiPairs.getD k (0,0))
    (sourceEtaBatch2304Lower k, sourceEtaBatch2304Upper k)
    (sourceBlock2304TwoPairs.getD k (0,0))

theorem sourceBlock2304Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2304XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2304+k):ℂ)).re ∧
      (xi (xiGridArgument (2304+k):ℂ)).re ≤ ((sourceBlock2304XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2304+k) _ _ _
    (sourceBlock2304PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2304_actual_enclosure k hk)
    (sourceBlock2304TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2304Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2304XiPair k).1 := by
  decide +kernel

theorem sourceBlock2304Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2304Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2304XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2304XiPair k)).2 ≤
      sourceBlock2304Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2304_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2304+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2304+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2304Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2304+k) (sourceBlock2304XiPair k) _
    (sourceBlock2304Xi_enclosure k hk) (sourceBlock2304Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2304Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2336_bound (k : ℕ) (hk : k < 2336) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2304
  · exact sourceRoundedMidpoint_first2304_bound k h
  · have hsum : 2304+(k-2304) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2304_bound (k-2304) (by omega)

end ReciprocalXi
