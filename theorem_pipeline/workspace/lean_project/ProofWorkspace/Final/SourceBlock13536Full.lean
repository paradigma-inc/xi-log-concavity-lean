import ProofWorkspace.Final.SourceBlock13504Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13536DataFull
import ProofWorkspace.Final.EtaBlock13536Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13536XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13536+k) (sourceBlock13536PiPairs.getD k (0,0))
    (sourceEtaBatch13536Lower k, sourceEtaBatch13536Upper k)
    (sourceBlock13536TwoPairs.getD k (0,0))

theorem sourceBlock13536Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13536XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13536+k):ℂ)).re ∧
      (xi (xiGridArgument (13536+k):ℂ)).re ≤ ((sourceBlock13536XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13536+k) _ _ _
    (sourceBlock13536PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13536_actual_enclosure k hk)
    (sourceBlock13536TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13536Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13536XiPair k).1 := by
  decide +kernel

theorem sourceBlock13536Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13536Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13536XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13536XiPair k)).2 ≤
      sourceBlock13536Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13536_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13536+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13536+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13536Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13536+k) (sourceBlock13536XiPair k) _
    (sourceBlock13536Xi_enclosure k hk) (sourceBlock13536Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13536Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13568_bound (k : ℕ) (hk : k < 13568) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13536
  · exact sourceRoundedMidpoint_first13536_bound k h
  · have hsum : 13536+(k-13536) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13536_bound (k-13536) (by omega)

end ReciprocalXi
