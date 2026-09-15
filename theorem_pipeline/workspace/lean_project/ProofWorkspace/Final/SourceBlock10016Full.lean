import ProofWorkspace.Final.SourceBlock9984Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10016DataFull
import ProofWorkspace.Final.EtaBlock10016Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10016XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10016+k) (sourceBlock10016PiPairs.getD k (0,0))
    (sourceEtaBatch10016Lower k, sourceEtaBatch10016Upper k)
    (sourceBlock10016TwoPairs.getD k (0,0))

theorem sourceBlock10016Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10016XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10016+k):ℂ)).re ∧
      (xi (xiGridArgument (10016+k):ℂ)).re ≤ ((sourceBlock10016XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10016+k) _ _ _
    (sourceBlock10016PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10016_actual_enclosure k hk)
    (sourceBlock10016TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10016Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10016XiPair k).1 := by
  decide +kernel

theorem sourceBlock10016Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10016Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10016XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10016XiPair k)).2 ≤
      sourceBlock10016Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10016_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10016+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10016+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10016Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10016+k) (sourceBlock10016XiPair k) _
    (sourceBlock10016Xi_enclosure k hk) (sourceBlock10016Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10016Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10048_bound (k : ℕ) (hk : k < 10048) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10016
  · exact sourceRoundedMidpoint_first10016_bound k h
  · have hsum : 10016+(k-10016) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10016_bound (k-10016) (by omega)

end ReciprocalXi
