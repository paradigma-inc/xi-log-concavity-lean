import ProofWorkspace.Final.SourceBlock1248Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1280DataFull
import ProofWorkspace.Final.EtaBlock1280Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1280XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1280+k) (sourceBlock1280PiPairs.getD k (0,0))
    (sourceEtaBatch1280Lower k, sourceEtaBatch1280Upper k)
    (sourceBlock1280TwoPairs.getD k (0,0))

theorem sourceBlock1280Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1280XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1280+k):ℂ)).re ∧
      (xi (xiGridArgument (1280+k):ℂ)).re ≤ ((sourceBlock1280XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1280+k) _ _ _
    (sourceBlock1280PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1280_actual_enclosure k hk)
    (sourceBlock1280TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1280Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1280XiPair k).1 := by
  decide +kernel

theorem sourceBlock1280Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1280Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1280XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1280XiPair k)).2 ≤
      sourceBlock1280Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1280_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1280+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1280+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1280Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1280+k) (sourceBlock1280XiPair k) _
    (sourceBlock1280Xi_enclosure k hk) (sourceBlock1280Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1280Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1312_bound (k : ℕ) (hk : k < 1312) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1280
  · exact sourceRoundedMidpoint_first1280_bound k h
  · have hsum : 1280+(k-1280) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1280_bound (k-1280) (by omega)

end ReciprocalXi
