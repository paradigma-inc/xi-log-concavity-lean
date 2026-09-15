import ProofWorkspace.Final.SourceBlock10496Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10528DataFull
import ProofWorkspace.Final.EtaBlock10528Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10528XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10528+k) (sourceBlock10528PiPairs.getD k (0,0))
    (sourceEtaBatch10528Lower k, sourceEtaBatch10528Upper k)
    (sourceBlock10528TwoPairs.getD k (0,0))

theorem sourceBlock10528Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10528XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10528+k):ℂ)).re ∧
      (xi (xiGridArgument (10528+k):ℂ)).re ≤ ((sourceBlock10528XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10528+k) _ _ _
    (sourceBlock10528PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10528_actual_enclosure k hk)
    (sourceBlock10528TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10528Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10528XiPair k).1 := by
  decide +kernel

theorem sourceBlock10528Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10528Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10528XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10528XiPair k)).2 ≤
      sourceBlock10528Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10528_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10528+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10528+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10528Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10528+k) (sourceBlock10528XiPair k) _
    (sourceBlock10528Xi_enclosure k hk) (sourceBlock10528Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10528Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10560_bound (k : ℕ) (hk : k < 10560) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10528
  · exact sourceRoundedMidpoint_first10528_bound k h
  · have hsum : 10528+(k-10528) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10528_bound (k-10528) (by omega)

end ReciprocalXi
