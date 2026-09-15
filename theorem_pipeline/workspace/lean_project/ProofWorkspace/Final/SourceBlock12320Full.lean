import ProofWorkspace.Final.SourceBlock12288Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12320DataFull
import ProofWorkspace.Final.EtaBlock12320Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12320XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12320+k) (sourceBlock12320PiPairs.getD k (0,0))
    (sourceEtaBatch12320Lower k, sourceEtaBatch12320Upper k)
    (sourceBlock12320TwoPairs.getD k (0,0))

theorem sourceBlock12320Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12320XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12320+k):ℂ)).re ∧
      (xi (xiGridArgument (12320+k):ℂ)).re ≤ ((sourceBlock12320XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12320+k) _ _ _
    (sourceBlock12320PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12320_actual_enclosure k hk)
    (sourceBlock12320TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12320Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12320XiPair k).1 := by
  decide +kernel

theorem sourceBlock12320Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12320Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12320XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12320XiPair k)).2 ≤
      sourceBlock12320Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12320_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12320+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12320+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12320Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12320+k) (sourceBlock12320XiPair k) _
    (sourceBlock12320Xi_enclosure k hk) (sourceBlock12320Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12320Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12352_bound (k : ℕ) (hk : k < 12352) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12320
  · exact sourceRoundedMidpoint_first12320_bound k h
  · have hsum : 12320+(k-12320) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12320_bound (k-12320) (by omega)

end ReciprocalXi
