import ProofWorkspace.Final.SourceBlock13216Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13248DataFull
import ProofWorkspace.Final.EtaBlock13248Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13248XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13248+k) (sourceBlock13248PiPairs.getD k (0,0))
    (sourceEtaBatch13248Lower k, sourceEtaBatch13248Upper k)
    (sourceBlock13248TwoPairs.getD k (0,0))

theorem sourceBlock13248Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13248XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13248+k):ℂ)).re ∧
      (xi (xiGridArgument (13248+k):ℂ)).re ≤ ((sourceBlock13248XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13248+k) _ _ _
    (sourceBlock13248PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13248_actual_enclosure k hk)
    (sourceBlock13248TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13248Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13248XiPair k).1 := by
  decide +kernel

theorem sourceBlock13248Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13248Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13248XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13248XiPair k)).2 ≤
      sourceBlock13248Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13248_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13248+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13248+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13248Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13248+k) (sourceBlock13248XiPair k) _
    (sourceBlock13248Xi_enclosure k hk) (sourceBlock13248Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13248Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13280_bound (k : ℕ) (hk : k < 13280) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13248
  · exact sourceRoundedMidpoint_first13248_bound k h
  · have hsum : 13248+(k-13248) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13248_bound (k-13248) (by omega)

end ReciprocalXi
