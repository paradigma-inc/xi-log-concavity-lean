import ProofWorkspace.Final.SourceBlock9696Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9728DataFull
import ProofWorkspace.Final.EtaBlock9728Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9728XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9728+k) (sourceBlock9728PiPairs.getD k (0,0))
    (sourceEtaBatch9728Lower k, sourceEtaBatch9728Upper k)
    (sourceBlock9728TwoPairs.getD k (0,0))

theorem sourceBlock9728Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9728XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9728+k):ℂ)).re ∧
      (xi (xiGridArgument (9728+k):ℂ)).re ≤ ((sourceBlock9728XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9728+k) _ _ _
    (sourceBlock9728PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9728_actual_enclosure k hk)
    (sourceBlock9728TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9728Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9728XiPair k).1 := by
  decide +kernel

theorem sourceBlock9728Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9728Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9728XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9728XiPair k)).2 ≤
      sourceBlock9728Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9728_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9728+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9728+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9728Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9728+k) (sourceBlock9728XiPair k) _
    (sourceBlock9728Xi_enclosure k hk) (sourceBlock9728Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9728Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9760_bound (k : ℕ) (hk : k < 9760) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9728
  · exact sourceRoundedMidpoint_first9728_bound k h
  · have hsum : 9728+(k-9728) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9728_bound (k-9728) (by omega)

end ReciprocalXi
