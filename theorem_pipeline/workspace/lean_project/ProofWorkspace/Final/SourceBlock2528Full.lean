import ProofWorkspace.Final.SourceBlock2496Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2528DataFull
import ProofWorkspace.Final.EtaBlock2528Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2528XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2528+k) (sourceBlock2528PiPairs.getD k (0,0))
    (sourceEtaBatch2528Lower k, sourceEtaBatch2528Upper k)
    (sourceBlock2528TwoPairs.getD k (0,0))

theorem sourceBlock2528Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2528XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2528+k):ℂ)).re ∧
      (xi (xiGridArgument (2528+k):ℂ)).re ≤ ((sourceBlock2528XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2528+k) _ _ _
    (sourceBlock2528PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2528_actual_enclosure k hk)
    (sourceBlock2528TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2528Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2528XiPair k).1 := by
  decide +kernel

theorem sourceBlock2528Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2528Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2528XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2528XiPair k)).2 ≤
      sourceBlock2528Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2528_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2528+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2528+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2528Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2528+k) (sourceBlock2528XiPair k) _
    (sourceBlock2528Xi_enclosure k hk) (sourceBlock2528Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2528Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2560_bound (k : ℕ) (hk : k < 2560) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2528
  · exact sourceRoundedMidpoint_first2528_bound k h
  · have hsum : 2528+(k-2528) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2528_bound (k-2528) (by omega)

end ReciprocalXi
