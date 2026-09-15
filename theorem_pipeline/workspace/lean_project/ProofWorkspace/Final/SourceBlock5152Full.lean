import ProofWorkspace.Final.SourceBlock5120Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5152DataFull
import ProofWorkspace.Final.EtaBlock5152Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5152XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5152+k) (sourceBlock5152PiPairs.getD k (0,0))
    (sourceEtaBatch5152Lower k, sourceEtaBatch5152Upper k)
    (sourceBlock5152TwoPairs.getD k (0,0))

theorem sourceBlock5152Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5152XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5152+k):ℂ)).re ∧
      (xi (xiGridArgument (5152+k):ℂ)).re ≤ ((sourceBlock5152XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5152+k) _ _ _
    (sourceBlock5152PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5152_actual_enclosure k hk)
    (sourceBlock5152TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5152Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5152XiPair k).1 := by
  decide +kernel

theorem sourceBlock5152Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5152Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5152XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5152XiPair k)).2 ≤
      sourceBlock5152Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5152_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5152+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5152+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5152Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5152+k) (sourceBlock5152XiPair k) _
    (sourceBlock5152Xi_enclosure k hk) (sourceBlock5152Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5152Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5184_bound (k : ℕ) (hk : k < 5184) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5152
  · exact sourceRoundedMidpoint_first5152_bound k h
  · have hsum : 5152+(k-5152) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5152_bound (k-5152) (by omega)

end ReciprocalXi
