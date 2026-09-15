import ProofWorkspace.Final.SourceBlock1472Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1504DataFull
import ProofWorkspace.Final.EtaBlock1504Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1504XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1504+k) (sourceBlock1504PiPairs.getD k (0,0))
    (sourceEtaBatch1504Lower k, sourceEtaBatch1504Upper k)
    (sourceBlock1504TwoPairs.getD k (0,0))

theorem sourceBlock1504Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1504XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1504+k):ℂ)).re ∧
      (xi (xiGridArgument (1504+k):ℂ)).re ≤ ((sourceBlock1504XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1504+k) _ _ _
    (sourceBlock1504PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1504_actual_enclosure k hk)
    (sourceBlock1504TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1504Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1504XiPair k).1 := by
  decide +kernel

theorem sourceBlock1504Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1504Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1504XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1504XiPair k)).2 ≤
      sourceBlock1504Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1504_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1504+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1504+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1504Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1504+k) (sourceBlock1504XiPair k) _
    (sourceBlock1504Xi_enclosure k hk) (sourceBlock1504Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1504Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1536_bound (k : ℕ) (hk : k < 1536) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1504
  · exact sourceRoundedMidpoint_first1504_bound k h
  · have hsum : 1504+(k-1504) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1504_bound (k-1504) (by omega)

end ReciprocalXi
