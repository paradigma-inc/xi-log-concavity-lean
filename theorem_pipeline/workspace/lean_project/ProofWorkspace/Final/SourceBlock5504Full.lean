import ProofWorkspace.Final.SourceBlock5472Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5504DataFull
import ProofWorkspace.Final.EtaBlock5504Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5504XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5504+k) (sourceBlock5504PiPairs.getD k (0,0))
    (sourceEtaBatch5504Lower k, sourceEtaBatch5504Upper k)
    (sourceBlock5504TwoPairs.getD k (0,0))

theorem sourceBlock5504Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5504XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5504+k):ℂ)).re ∧
      (xi (xiGridArgument (5504+k):ℂ)).re ≤ ((sourceBlock5504XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5504+k) _ _ _
    (sourceBlock5504PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5504_actual_enclosure k hk)
    (sourceBlock5504TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5504Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5504XiPair k).1 := by
  decide +kernel

theorem sourceBlock5504Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5504Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5504XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5504XiPair k)).2 ≤
      sourceBlock5504Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5504_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5504+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5504+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5504Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5504+k) (sourceBlock5504XiPair k) _
    (sourceBlock5504Xi_enclosure k hk) (sourceBlock5504Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5504Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5536_bound (k : ℕ) (hk : k < 5536) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5504
  · exact sourceRoundedMidpoint_first5504_bound k h
  · have hsum : 5504+(k-5504) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5504_bound (k-5504) (by omega)

end ReciprocalXi
