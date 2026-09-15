import ProofWorkspace.Final.SourceBlock10240Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10272DataFull
import ProofWorkspace.Final.EtaBlock10272Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10272XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10272+k) (sourceBlock10272PiPairs.getD k (0,0))
    (sourceEtaBatch10272Lower k, sourceEtaBatch10272Upper k)
    (sourceBlock10272TwoPairs.getD k (0,0))

theorem sourceBlock10272Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10272XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10272+k):ℂ)).re ∧
      (xi (xiGridArgument (10272+k):ℂ)).re ≤ ((sourceBlock10272XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10272+k) _ _ _
    (sourceBlock10272PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10272_actual_enclosure k hk)
    (sourceBlock10272TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10272Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10272XiPair k).1 := by
  decide +kernel

theorem sourceBlock10272Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10272Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10272XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10272XiPair k)).2 ≤
      sourceBlock10272Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10272_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10272+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10272+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10272Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10272+k) (sourceBlock10272XiPair k) _
    (sourceBlock10272Xi_enclosure k hk) (sourceBlock10272Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10272Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10304_bound (k : ℕ) (hk : k < 10304) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10272
  · exact sourceRoundedMidpoint_first10272_bound k h
  · have hsum : 10272+(k-10272) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10272_bound (k-10272) (by omega)

end ReciprocalXi
