import ProofWorkspace.Final.SourceBlock1312Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1344DataFull
import ProofWorkspace.Final.EtaBlock1344Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1344XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1344+k) (sourceBlock1344PiPairs.getD k (0,0))
    (sourceEtaBatch1344Lower k, sourceEtaBatch1344Upper k)
    (sourceBlock1344TwoPairs.getD k (0,0))

theorem sourceBlock1344Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1344XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1344+k):ℂ)).re ∧
      (xi (xiGridArgument (1344+k):ℂ)).re ≤ ((sourceBlock1344XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1344+k) _ _ _
    (sourceBlock1344PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1344_actual_enclosure k hk)
    (sourceBlock1344TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1344Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1344XiPair k).1 := by
  decide +kernel

theorem sourceBlock1344Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1344Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1344XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1344XiPair k)).2 ≤
      sourceBlock1344Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1344_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1344+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1344+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1344Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1344+k) (sourceBlock1344XiPair k) _
    (sourceBlock1344Xi_enclosure k hk) (sourceBlock1344Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1344Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1376_bound (k : ℕ) (hk : k < 1376) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1344
  · exact sourceRoundedMidpoint_first1344_bound k h
  · have hsum : 1344+(k-1344) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1344_bound (k-1344) (by omega)

end ReciprocalXi
