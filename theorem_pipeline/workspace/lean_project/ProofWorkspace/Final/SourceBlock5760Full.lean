import ProofWorkspace.Final.SourceBlock5728Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5760DataFull
import ProofWorkspace.Final.EtaBlock5760Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5760XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5760+k) (sourceBlock5760PiPairs.getD k (0,0))
    (sourceEtaBatch5760Lower k, sourceEtaBatch5760Upper k)
    (sourceBlock5760TwoPairs.getD k (0,0))

theorem sourceBlock5760Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5760XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5760+k):ℂ)).re ∧
      (xi (xiGridArgument (5760+k):ℂ)).re ≤ ((sourceBlock5760XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5760+k) _ _ _
    (sourceBlock5760PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5760_actual_enclosure k hk)
    (sourceBlock5760TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5760Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5760XiPair k).1 := by
  decide +kernel

theorem sourceBlock5760Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5760Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5760XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5760XiPair k)).2 ≤
      sourceBlock5760Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5760_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5760+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5760+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5760Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5760+k) (sourceBlock5760XiPair k) _
    (sourceBlock5760Xi_enclosure k hk) (sourceBlock5760Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5760Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5792_bound (k : ℕ) (hk : k < 5792) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5760
  · exact sourceRoundedMidpoint_first5760_bound k h
  · have hsum : 5760+(k-5760) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5760_bound (k-5760) (by omega)

end ReciprocalXi
