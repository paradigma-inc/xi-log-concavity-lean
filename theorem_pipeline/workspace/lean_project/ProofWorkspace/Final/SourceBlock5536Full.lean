import ProofWorkspace.Final.SourceBlock5504Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5536DataFull
import ProofWorkspace.Final.EtaBlock5536Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5536XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5536+k) (sourceBlock5536PiPairs.getD k (0,0))
    (sourceEtaBatch5536Lower k, sourceEtaBatch5536Upper k)
    (sourceBlock5536TwoPairs.getD k (0,0))

theorem sourceBlock5536Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5536XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5536+k):ℂ)).re ∧
      (xi (xiGridArgument (5536+k):ℂ)).re ≤ ((sourceBlock5536XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5536+k) _ _ _
    (sourceBlock5536PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5536_actual_enclosure k hk)
    (sourceBlock5536TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5536Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5536XiPair k).1 := by
  decide +kernel

theorem sourceBlock5536Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5536Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5536XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5536XiPair k)).2 ≤
      sourceBlock5536Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5536_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5536+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5536+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5536Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5536+k) (sourceBlock5536XiPair k) _
    (sourceBlock5536Xi_enclosure k hk) (sourceBlock5536Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5536Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5568_bound (k : ℕ) (hk : k < 5568) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5536
  · exact sourceRoundedMidpoint_first5536_bound k h
  · have hsum : 5536+(k-5536) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5536_bound (k-5536) (by omega)

end ReciprocalXi
