import ProofWorkspace.Final.SourceBlock5632Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5664DataFull
import ProofWorkspace.Final.EtaBlock5664Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5664XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5664+k) (sourceBlock5664PiPairs.getD k (0,0))
    (sourceEtaBatch5664Lower k, sourceEtaBatch5664Upper k)
    (sourceBlock5664TwoPairs.getD k (0,0))

theorem sourceBlock5664Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5664XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5664+k):ℂ)).re ∧
      (xi (xiGridArgument (5664+k):ℂ)).re ≤ ((sourceBlock5664XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5664+k) _ _ _
    (sourceBlock5664PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5664_actual_enclosure k hk)
    (sourceBlock5664TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5664Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5664XiPair k).1 := by
  decide +kernel

theorem sourceBlock5664Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5664Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5664XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5664XiPair k)).2 ≤
      sourceBlock5664Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5664_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5664+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5664+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5664Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5664+k) (sourceBlock5664XiPair k) _
    (sourceBlock5664Xi_enclosure k hk) (sourceBlock5664Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5664Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5696_bound (k : ℕ) (hk : k < 5696) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5664
  · exact sourceRoundedMidpoint_first5664_bound k h
  · have hsum : 5664+(k-5664) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5664_bound (k-5664) (by omega)

end ReciprocalXi
