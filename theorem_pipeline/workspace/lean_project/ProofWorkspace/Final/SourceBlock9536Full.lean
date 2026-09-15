import ProofWorkspace.Final.SourceBlock9504Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9536DataFull
import ProofWorkspace.Final.EtaBlock9536Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9536XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9536+k) (sourceBlock9536PiPairs.getD k (0,0))
    (sourceEtaBatch9536Lower k, sourceEtaBatch9536Upper k)
    (sourceBlock9536TwoPairs.getD k (0,0))

theorem sourceBlock9536Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9536XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9536+k):ℂ)).re ∧
      (xi (xiGridArgument (9536+k):ℂ)).re ≤ ((sourceBlock9536XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9536+k) _ _ _
    (sourceBlock9536PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9536_actual_enclosure k hk)
    (sourceBlock9536TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9536Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9536XiPair k).1 := by
  decide +kernel

theorem sourceBlock9536Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9536Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9536XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9536XiPair k)).2 ≤
      sourceBlock9536Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9536_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9536+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9536+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9536Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9536+k) (sourceBlock9536XiPair k) _
    (sourceBlock9536Xi_enclosure k hk) (sourceBlock9536Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9536Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9568_bound (k : ℕ) (hk : k < 9568) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9536
  · exact sourceRoundedMidpoint_first9536_bound k h
  · have hsum : 9536+(k-9536) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9536_bound (k-9536) (by omega)

end ReciprocalXi
