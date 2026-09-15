import ProofWorkspace.Final.SourceBlock5600Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5632DataFull
import ProofWorkspace.Final.EtaBlock5632Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5632XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5632+k) (sourceBlock5632PiPairs.getD k (0,0))
    (sourceEtaBatch5632Lower k, sourceEtaBatch5632Upper k)
    (sourceBlock5632TwoPairs.getD k (0,0))

theorem sourceBlock5632Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5632XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5632+k):ℂ)).re ∧
      (xi (xiGridArgument (5632+k):ℂ)).re ≤ ((sourceBlock5632XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5632+k) _ _ _
    (sourceBlock5632PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5632_actual_enclosure k hk)
    (sourceBlock5632TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5632Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5632XiPair k).1 := by
  decide +kernel

theorem sourceBlock5632Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5632Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5632XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5632XiPair k)).2 ≤
      sourceBlock5632Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5632_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5632+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5632+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5632Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5632+k) (sourceBlock5632XiPair k) _
    (sourceBlock5632Xi_enclosure k hk) (sourceBlock5632Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5632Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5664_bound (k : ℕ) (hk : k < 5664) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5632
  · exact sourceRoundedMidpoint_first5632_bound k h
  · have hsum : 5632+(k-5632) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5632_bound (k-5632) (by omega)

end ReciprocalXi
