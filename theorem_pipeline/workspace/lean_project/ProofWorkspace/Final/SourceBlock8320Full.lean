import ProofWorkspace.Final.SourceBlock8288Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8320DataFull
import ProofWorkspace.Final.EtaBlock8320Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8320XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8320+k) (sourceBlock8320PiPairs.getD k (0,0))
    (sourceEtaBatch8320Lower k, sourceEtaBatch8320Upper k)
    (sourceBlock8320TwoPairs.getD k (0,0))

theorem sourceBlock8320Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8320XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8320+k):ℂ)).re ∧
      (xi (xiGridArgument (8320+k):ℂ)).re ≤ ((sourceBlock8320XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8320+k) _ _ _
    (sourceBlock8320PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8320_actual_enclosure k hk)
    (sourceBlock8320TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8320Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8320XiPair k).1 := by
  decide +kernel

theorem sourceBlock8320Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8320Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8320XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8320XiPair k)).2 ≤
      sourceBlock8320Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8320_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8320+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8320+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8320Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8320+k) (sourceBlock8320XiPair k) _
    (sourceBlock8320Xi_enclosure k hk) (sourceBlock8320Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8320Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8352_bound (k : ℕ) (hk : k < 8352) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8320
  · exact sourceRoundedMidpoint_first8320_bound k h
  · have hsum : 8320+(k-8320) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8320_bound (k-8320) (by omega)

end ReciprocalXi
