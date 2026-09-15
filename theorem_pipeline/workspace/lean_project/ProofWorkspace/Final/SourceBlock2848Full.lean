import ProofWorkspace.Final.SourceBlock2816Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2848DataFull
import ProofWorkspace.Final.EtaBlock2848Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2848XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2848+k) (sourceBlock2848PiPairs.getD k (0,0))
    (sourceEtaBatch2848Lower k, sourceEtaBatch2848Upper k)
    (sourceBlock2848TwoPairs.getD k (0,0))

theorem sourceBlock2848Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2848XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2848+k):ℂ)).re ∧
      (xi (xiGridArgument (2848+k):ℂ)).re ≤ ((sourceBlock2848XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2848+k) _ _ _
    (sourceBlock2848PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2848_actual_enclosure k hk)
    (sourceBlock2848TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2848Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2848XiPair k).1 := by
  decide +kernel

theorem sourceBlock2848Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2848Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2848XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2848XiPair k)).2 ≤
      sourceBlock2848Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2848_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2848+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2848+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2848Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2848+k) (sourceBlock2848XiPair k) _
    (sourceBlock2848Xi_enclosure k hk) (sourceBlock2848Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2848Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2880_bound (k : ℕ) (hk : k < 2880) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2848
  · exact sourceRoundedMidpoint_first2848_bound k h
  · have hsum : 2848+(k-2848) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2848_bound (k-2848) (by omega)

end ReciprocalXi
