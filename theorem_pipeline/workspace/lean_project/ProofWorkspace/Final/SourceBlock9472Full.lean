import ProofWorkspace.Final.SourceBlock9440Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9472DataFull
import ProofWorkspace.Final.EtaBlock9472Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9472XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9472+k) (sourceBlock9472PiPairs.getD k (0,0))
    (sourceEtaBatch9472Lower k, sourceEtaBatch9472Upper k)
    (sourceBlock9472TwoPairs.getD k (0,0))

theorem sourceBlock9472Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9472XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9472+k):ℂ)).re ∧
      (xi (xiGridArgument (9472+k):ℂ)).re ≤ ((sourceBlock9472XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9472+k) _ _ _
    (sourceBlock9472PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9472_actual_enclosure k hk)
    (sourceBlock9472TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9472Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9472XiPair k).1 := by
  decide +kernel

theorem sourceBlock9472Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9472Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9472XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9472XiPair k)).2 ≤
      sourceBlock9472Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9472_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9472+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9472+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9472Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9472+k) (sourceBlock9472XiPair k) _
    (sourceBlock9472Xi_enclosure k hk) (sourceBlock9472Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9472Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9504_bound (k : ℕ) (hk : k < 9504) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9472
  · exact sourceRoundedMidpoint_first9472_bound k h
  · have hsum : 9472+(k-9472) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9472_bound (k-9472) (by omega)

end ReciprocalXi
