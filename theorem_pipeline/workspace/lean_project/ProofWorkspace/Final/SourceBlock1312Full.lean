import ProofWorkspace.Final.SourceBlock1280Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1312DataFull
import ProofWorkspace.Final.EtaBlock1312Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1312XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1312+k) (sourceBlock1312PiPairs.getD k (0,0))
    (sourceEtaBatch1312Lower k, sourceEtaBatch1312Upper k)
    (sourceBlock1312TwoPairs.getD k (0,0))

theorem sourceBlock1312Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1312XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1312+k):ℂ)).re ∧
      (xi (xiGridArgument (1312+k):ℂ)).re ≤ ((sourceBlock1312XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1312+k) _ _ _
    (sourceBlock1312PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1312_actual_enclosure k hk)
    (sourceBlock1312TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1312Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1312XiPair k).1 := by
  decide +kernel

theorem sourceBlock1312Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1312Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1312XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1312XiPair k)).2 ≤
      sourceBlock1312Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1312_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1312+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1312+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1312Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1312+k) (sourceBlock1312XiPair k) _
    (sourceBlock1312Xi_enclosure k hk) (sourceBlock1312Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1312Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1344_bound (k : ℕ) (hk : k < 1344) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1312
  · exact sourceRoundedMidpoint_first1312_bound k h
  · have hsum : 1312+(k-1312) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1312_bound (k-1312) (by omega)

end ReciprocalXi
