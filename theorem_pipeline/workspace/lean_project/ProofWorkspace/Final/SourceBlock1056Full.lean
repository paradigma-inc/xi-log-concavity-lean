import ProofWorkspace.Final.SourceBlock1024Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1056DataFull
import ProofWorkspace.Final.EtaBlock1056Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1056XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1056+k) (sourceBlock1056PiPairs.getD k (0,0))
    (sourceEtaBatch1056Lower k, sourceEtaBatch1056Upper k)
    (sourceBlock1056TwoPairs.getD k (0,0))

theorem sourceBlock1056Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1056XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1056+k):ℂ)).re ∧
      (xi (xiGridArgument (1056+k):ℂ)).re ≤ ((sourceBlock1056XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1056+k) _ _ _
    (sourceBlock1056PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1056_actual_enclosure k hk)
    (sourceBlock1056TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1056Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1056XiPair k).1 := by
  decide +kernel

theorem sourceBlock1056Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1056Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1056XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1056XiPair k)).2 ≤
      sourceBlock1056Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1056_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1056+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1056+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1056Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1056+k) (sourceBlock1056XiPair k) _
    (sourceBlock1056Xi_enclosure k hk) (sourceBlock1056Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1056Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1088_bound (k : ℕ) (hk : k < 1088) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1056
  · exact sourceRoundedMidpoint_first1056_bound k h
  · have hsum : 1056+(k-1056) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1056_bound (k-1056) (by omega)

end ReciprocalXi
