import ProofWorkspace.Final.SourceBlock7296Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7328DataFull
import ProofWorkspace.Final.EtaBlock7328Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7328XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7328+k) (sourceBlock7328PiPairs.getD k (0,0))
    (sourceEtaBatch7328Lower k, sourceEtaBatch7328Upper k)
    (sourceBlock7328TwoPairs.getD k (0,0))

theorem sourceBlock7328Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7328XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7328+k):ℂ)).re ∧
      (xi (xiGridArgument (7328+k):ℂ)).re ≤ ((sourceBlock7328XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7328+k) _ _ _
    (sourceBlock7328PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7328_actual_enclosure k hk)
    (sourceBlock7328TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7328Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7328XiPair k).1 := by
  decide +kernel

theorem sourceBlock7328Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7328Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7328XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7328XiPair k)).2 ≤
      sourceBlock7328Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7328_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7328+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7328+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7328Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7328+k) (sourceBlock7328XiPair k) _
    (sourceBlock7328Xi_enclosure k hk) (sourceBlock7328Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7328Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7360_bound (k : ℕ) (hk : k < 7360) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7328
  · exact sourceRoundedMidpoint_first7328_bound k h
  · have hsum : 7328+(k-7328) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7328_bound (k-7328) (by omega)

end ReciprocalXi
