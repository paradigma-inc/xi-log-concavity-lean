import ProofWorkspace.Final.SourceBlock4288Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4320DataFull
import ProofWorkspace.Final.EtaBlock4320Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4320XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4320+k) (sourceBlock4320PiPairs.getD k (0,0))
    (sourceEtaBatch4320Lower k, sourceEtaBatch4320Upper k)
    (sourceBlock4320TwoPairs.getD k (0,0))

theorem sourceBlock4320Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4320XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4320+k):ℂ)).re ∧
      (xi (xiGridArgument (4320+k):ℂ)).re ≤ ((sourceBlock4320XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4320+k) _ _ _
    (sourceBlock4320PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4320_actual_enclosure k hk)
    (sourceBlock4320TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4320Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4320XiPair k).1 := by
  decide +kernel

theorem sourceBlock4320Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4320Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4320XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4320XiPair k)).2 ≤
      sourceBlock4320Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4320_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4320+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4320+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4320Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4320+k) (sourceBlock4320XiPair k) _
    (sourceBlock4320Xi_enclosure k hk) (sourceBlock4320Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4320Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4352_bound (k : ℕ) (hk : k < 4352) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4320
  · exact sourceRoundedMidpoint_first4320_bound k h
  · have hsum : 4320+(k-4320) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4320_bound (k-4320) (by omega)

end ReciprocalXi
