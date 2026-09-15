import ProofWorkspace.Final.SourceBlock5664Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5696DataFull
import ProofWorkspace.Final.EtaBlock5696Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5696XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5696+k) (sourceBlock5696PiPairs.getD k (0,0))
    (sourceEtaBatch5696Lower k, sourceEtaBatch5696Upper k)
    (sourceBlock5696TwoPairs.getD k (0,0))

theorem sourceBlock5696Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5696XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5696+k):ℂ)).re ∧
      (xi (xiGridArgument (5696+k):ℂ)).re ≤ ((sourceBlock5696XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5696+k) _ _ _
    (sourceBlock5696PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5696_actual_enclosure k hk)
    (sourceBlock5696TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5696Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5696XiPair k).1 := by
  decide +kernel

theorem sourceBlock5696Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5696Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5696XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5696XiPair k)).2 ≤
      sourceBlock5696Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5696_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5696+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5696+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5696Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5696+k) (sourceBlock5696XiPair k) _
    (sourceBlock5696Xi_enclosure k hk) (sourceBlock5696Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5696Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5728_bound (k : ℕ) (hk : k < 5728) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5696
  · exact sourceRoundedMidpoint_first5696_bound k h
  · have hsum : 5696+(k-5696) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5696_bound (k-5696) (by omega)

end ReciprocalXi
