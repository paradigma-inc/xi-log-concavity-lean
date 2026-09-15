import ProofWorkspace.Final.SourceBlock2368Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2400DataFull
import ProofWorkspace.Final.EtaBlock2400Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2400XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2400+k) (sourceBlock2400PiPairs.getD k (0,0))
    (sourceEtaBatch2400Lower k, sourceEtaBatch2400Upper k)
    (sourceBlock2400TwoPairs.getD k (0,0))

theorem sourceBlock2400Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2400XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2400+k):ℂ)).re ∧
      (xi (xiGridArgument (2400+k):ℂ)).re ≤ ((sourceBlock2400XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2400+k) _ _ _
    (sourceBlock2400PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2400_actual_enclosure k hk)
    (sourceBlock2400TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2400Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2400XiPair k).1 := by
  decide +kernel

theorem sourceBlock2400Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2400Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2400XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2400XiPair k)).2 ≤
      sourceBlock2400Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2400_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2400+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2400+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2400Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2400+k) (sourceBlock2400XiPair k) _
    (sourceBlock2400Xi_enclosure k hk) (sourceBlock2400Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2400Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2432_bound (k : ℕ) (hk : k < 2432) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2400
  · exact sourceRoundedMidpoint_first2400_bound k h
  · have hsum : 2400+(k-2400) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2400_bound (k-2400) (by omega)

end ReciprocalXi
