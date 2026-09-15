import ProofWorkspace.Final.SourceBlock1120Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1152DataFull
import ProofWorkspace.Final.EtaBlock1152Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1152XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1152+k) (sourceBlock1152PiPairs.getD k (0,0))
    (sourceEtaBatch1152Lower k, sourceEtaBatch1152Upper k)
    (sourceBlock1152TwoPairs.getD k (0,0))

theorem sourceBlock1152Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1152XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1152+k):ℂ)).re ∧
      (xi (xiGridArgument (1152+k):ℂ)).re ≤ ((sourceBlock1152XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1152+k) _ _ _
    (sourceBlock1152PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1152_actual_enclosure k hk)
    (sourceBlock1152TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1152Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1152XiPair k).1 := by
  decide +kernel

theorem sourceBlock1152Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1152Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1152XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1152XiPair k)).2 ≤
      sourceBlock1152Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1152_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1152+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1152+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1152Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1152+k) (sourceBlock1152XiPair k) _
    (sourceBlock1152Xi_enclosure k hk) (sourceBlock1152Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1152Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1184_bound (k : ℕ) (hk : k < 1184) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1152
  · exact sourceRoundedMidpoint_first1152_bound k h
  · have hsum : 1152+(k-1152) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1152_bound (k-1152) (by omega)

end ReciprocalXi
