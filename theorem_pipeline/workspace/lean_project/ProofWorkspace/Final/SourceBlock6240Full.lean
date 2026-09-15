import ProofWorkspace.Final.SourceBlock6208Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6240DataFull
import ProofWorkspace.Final.EtaBlock6240Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6240XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6240+k) (sourceBlock6240PiPairs.getD k (0,0))
    (sourceEtaBatch6240Lower k, sourceEtaBatch6240Upper k)
    (sourceBlock6240TwoPairs.getD k (0,0))

theorem sourceBlock6240Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6240XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6240+k):ℂ)).re ∧
      (xi (xiGridArgument (6240+k):ℂ)).re ≤ ((sourceBlock6240XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6240+k) _ _ _
    (sourceBlock6240PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6240_actual_enclosure k hk)
    (sourceBlock6240TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6240Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6240XiPair k).1 := by
  decide +kernel

theorem sourceBlock6240Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6240Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6240XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6240XiPair k)).2 ≤
      sourceBlock6240Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6240_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6240+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6240+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6240Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6240+k) (sourceBlock6240XiPair k) _
    (sourceBlock6240Xi_enclosure k hk) (sourceBlock6240Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6240Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6272_bound (k : ℕ) (hk : k < 6272) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6240
  · exact sourceRoundedMidpoint_first6240_bound k h
  · have hsum : 6240+(k-6240) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6240_bound (k-6240) (by omega)

end ReciprocalXi
