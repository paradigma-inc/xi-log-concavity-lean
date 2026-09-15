import ProofWorkspace.Final.SourceBlock9728Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9760DataFull
import ProofWorkspace.Final.EtaBlock9760Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9760XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9760+k) (sourceBlock9760PiPairs.getD k (0,0))
    (sourceEtaBatch9760Lower k, sourceEtaBatch9760Upper k)
    (sourceBlock9760TwoPairs.getD k (0,0))

theorem sourceBlock9760Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9760XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9760+k):ℂ)).re ∧
      (xi (xiGridArgument (9760+k):ℂ)).re ≤ ((sourceBlock9760XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9760+k) _ _ _
    (sourceBlock9760PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9760_actual_enclosure k hk)
    (sourceBlock9760TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9760Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9760XiPair k).1 := by
  decide +kernel

theorem sourceBlock9760Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9760Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9760XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9760XiPair k)).2 ≤
      sourceBlock9760Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9760_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9760+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9760+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9760Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9760+k) (sourceBlock9760XiPair k) _
    (sourceBlock9760Xi_enclosure k hk) (sourceBlock9760Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9760Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9792_bound (k : ℕ) (hk : k < 9792) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9760
  · exact sourceRoundedMidpoint_first9760_bound k h
  · have hsum : 9760+(k-9760) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9760_bound (k-9760) (by omega)

end ReciprocalXi
