import ProofWorkspace.Final.SourceBlock1344Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1376DataFull
import ProofWorkspace.Final.EtaBlock1376Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1376XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1376+k) (sourceBlock1376PiPairs.getD k (0,0))
    (sourceEtaBatch1376Lower k, sourceEtaBatch1376Upper k)
    (sourceBlock1376TwoPairs.getD k (0,0))

theorem sourceBlock1376Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1376XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1376+k):ℂ)).re ∧
      (xi (xiGridArgument (1376+k):ℂ)).re ≤ ((sourceBlock1376XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1376+k) _ _ _
    (sourceBlock1376PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1376_actual_enclosure k hk)
    (sourceBlock1376TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1376Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1376XiPair k).1 := by
  decide +kernel

theorem sourceBlock1376Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1376Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1376XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1376XiPair k)).2 ≤
      sourceBlock1376Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1376_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1376+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1376+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1376Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1376+k) (sourceBlock1376XiPair k) _
    (sourceBlock1376Xi_enclosure k hk) (sourceBlock1376Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1376Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1408_bound (k : ℕ) (hk : k < 1408) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1376
  · exact sourceRoundedMidpoint_first1376_bound k h
  · have hsum : 1376+(k-1376) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1376_bound (k-1376) (by omega)

end ReciprocalXi
