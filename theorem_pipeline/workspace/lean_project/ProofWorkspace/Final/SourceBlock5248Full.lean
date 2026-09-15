import ProofWorkspace.Final.SourceBlock5216Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5248DataFull
import ProofWorkspace.Final.EtaBlock5248Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5248XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5248+k) (sourceBlock5248PiPairs.getD k (0,0))
    (sourceEtaBatch5248Lower k, sourceEtaBatch5248Upper k)
    (sourceBlock5248TwoPairs.getD k (0,0))

theorem sourceBlock5248Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5248XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5248+k):ℂ)).re ∧
      (xi (xiGridArgument (5248+k):ℂ)).re ≤ ((sourceBlock5248XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5248+k) _ _ _
    (sourceBlock5248PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5248_actual_enclosure k hk)
    (sourceBlock5248TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5248Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5248XiPair k).1 := by
  decide +kernel

theorem sourceBlock5248Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5248Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5248XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5248XiPair k)).2 ≤
      sourceBlock5248Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5248_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5248+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5248+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5248Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5248+k) (sourceBlock5248XiPair k) _
    (sourceBlock5248Xi_enclosure k hk) (sourceBlock5248Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5248Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5280_bound (k : ℕ) (hk : k < 5280) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5248
  · exact sourceRoundedMidpoint_first5248_bound k h
  · have hsum : 5248+(k-5248) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5248_bound (k-5248) (by omega)

end ReciprocalXi
