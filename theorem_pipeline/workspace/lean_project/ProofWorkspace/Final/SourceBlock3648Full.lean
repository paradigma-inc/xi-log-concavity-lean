import ProofWorkspace.Final.SourceBlock3616Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3648DataFull
import ProofWorkspace.Final.EtaBlock3648Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3648XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3648+k) (sourceBlock3648PiPairs.getD k (0,0))
    (sourceEtaBatch3648Lower k, sourceEtaBatch3648Upper k)
    (sourceBlock3648TwoPairs.getD k (0,0))

theorem sourceBlock3648Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3648XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3648+k):ℂ)).re ∧
      (xi (xiGridArgument (3648+k):ℂ)).re ≤ ((sourceBlock3648XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3648+k) _ _ _
    (sourceBlock3648PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3648_actual_enclosure k hk)
    (sourceBlock3648TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3648Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3648XiPair k).1 := by
  decide +kernel

theorem sourceBlock3648Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3648Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3648XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3648XiPair k)).2 ≤
      sourceBlock3648Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3648_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3648+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3648+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3648Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3648+k) (sourceBlock3648XiPair k) _
    (sourceBlock3648Xi_enclosure k hk) (sourceBlock3648Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3648Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3680_bound (k : ℕ) (hk : k < 3680) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3648
  · exact sourceRoundedMidpoint_first3648_bound k h
  · have hsum : 3648+(k-3648) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3648_bound (k-3648) (by omega)

end ReciprocalXi
