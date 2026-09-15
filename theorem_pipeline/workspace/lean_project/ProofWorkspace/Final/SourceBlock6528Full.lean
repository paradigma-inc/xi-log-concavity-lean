import ProofWorkspace.Final.SourceBlock6496Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6528DataFull
import ProofWorkspace.Final.EtaBlock6528Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6528XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6528+k) (sourceBlock6528PiPairs.getD k (0,0))
    (sourceEtaBatch6528Lower k, sourceEtaBatch6528Upper k)
    (sourceBlock6528TwoPairs.getD k (0,0))

theorem sourceBlock6528Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6528XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6528+k):ℂ)).re ∧
      (xi (xiGridArgument (6528+k):ℂ)).re ≤ ((sourceBlock6528XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6528+k) _ _ _
    (sourceBlock6528PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6528_actual_enclosure k hk)
    (sourceBlock6528TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6528Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6528XiPair k).1 := by
  decide +kernel

theorem sourceBlock6528Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6528Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6528XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6528XiPair k)).2 ≤
      sourceBlock6528Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6528_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6528+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6528+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6528Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6528+k) (sourceBlock6528XiPair k) _
    (sourceBlock6528Xi_enclosure k hk) (sourceBlock6528Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6528Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6560_bound (k : ℕ) (hk : k < 6560) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6528
  · exact sourceRoundedMidpoint_first6528_bound k h
  · have hsum : 6528+(k-6528) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6528_bound (k-6528) (by omega)

end ReciprocalXi
