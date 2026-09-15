import ProofWorkspace.Final.SourceBlock5696Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5728DataFull
import ProofWorkspace.Final.EtaBlock5728Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5728XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5728+k) (sourceBlock5728PiPairs.getD k (0,0))
    (sourceEtaBatch5728Lower k, sourceEtaBatch5728Upper k)
    (sourceBlock5728TwoPairs.getD k (0,0))

theorem sourceBlock5728Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5728XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5728+k):ℂ)).re ∧
      (xi (xiGridArgument (5728+k):ℂ)).re ≤ ((sourceBlock5728XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5728+k) _ _ _
    (sourceBlock5728PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5728_actual_enclosure k hk)
    (sourceBlock5728TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5728Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5728XiPair k).1 := by
  decide +kernel

theorem sourceBlock5728Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5728Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5728XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5728XiPair k)).2 ≤
      sourceBlock5728Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5728_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5728+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5728+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5728Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5728+k) (sourceBlock5728XiPair k) _
    (sourceBlock5728Xi_enclosure k hk) (sourceBlock5728Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5728Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5760_bound (k : ℕ) (hk : k < 5760) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5728
  · exact sourceRoundedMidpoint_first5728_bound k h
  · have hsum : 5728+(k-5728) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5728_bound (k-5728) (by omega)

end ReciprocalXi
