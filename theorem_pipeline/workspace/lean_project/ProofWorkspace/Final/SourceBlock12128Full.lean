import ProofWorkspace.Final.SourceBlock12096Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12128DataFull
import ProofWorkspace.Final.EtaBlock12128Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12128XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12128+k) (sourceBlock12128PiPairs.getD k (0,0))
    (sourceEtaBatch12128Lower k, sourceEtaBatch12128Upper k)
    (sourceBlock12128TwoPairs.getD k (0,0))

theorem sourceBlock12128Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12128XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12128+k):ℂ)).re ∧
      (xi (xiGridArgument (12128+k):ℂ)).re ≤ ((sourceBlock12128XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12128+k) _ _ _
    (sourceBlock12128PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12128_actual_enclosure k hk)
    (sourceBlock12128TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12128Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12128XiPair k).1 := by
  decide +kernel

theorem sourceBlock12128Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12128Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12128XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12128XiPair k)).2 ≤
      sourceBlock12128Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12128_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12128+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12128+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12128Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12128+k) (sourceBlock12128XiPair k) _
    (sourceBlock12128Xi_enclosure k hk) (sourceBlock12128Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12128Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12160_bound (k : ℕ) (hk : k < 12160) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12128
  · exact sourceRoundedMidpoint_first12128_bound k h
  · have hsum : 12128+(k-12128) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12128_bound (k-12128) (by omega)

end ReciprocalXi
