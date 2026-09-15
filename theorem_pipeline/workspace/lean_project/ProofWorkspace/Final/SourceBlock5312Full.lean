import ProofWorkspace.Final.SourceBlock5280Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5312DataFull
import ProofWorkspace.Final.EtaBlock5312Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5312XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5312+k) (sourceBlock5312PiPairs.getD k (0,0))
    (sourceEtaBatch5312Lower k, sourceEtaBatch5312Upper k)
    (sourceBlock5312TwoPairs.getD k (0,0))

theorem sourceBlock5312Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5312XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5312+k):ℂ)).re ∧
      (xi (xiGridArgument (5312+k):ℂ)).re ≤ ((sourceBlock5312XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5312+k) _ _ _
    (sourceBlock5312PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5312_actual_enclosure k hk)
    (sourceBlock5312TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5312Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5312XiPair k).1 := by
  decide +kernel

theorem sourceBlock5312Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5312Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5312XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5312XiPair k)).2 ≤
      sourceBlock5312Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5312_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5312+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5312+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5312Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5312+k) (sourceBlock5312XiPair k) _
    (sourceBlock5312Xi_enclosure k hk) (sourceBlock5312Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5312Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5344_bound (k : ℕ) (hk : k < 5344) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5312
  · exact sourceRoundedMidpoint_first5312_bound k h
  · have hsum : 5312+(k-5312) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5312_bound (k-5312) (by omega)

end ReciprocalXi
