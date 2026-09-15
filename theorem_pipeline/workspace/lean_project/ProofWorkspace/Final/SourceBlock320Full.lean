import ProofWorkspace.Final.SourceBlock288Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock320DataFull
import ProofWorkspace.Final.EtaBlock320Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock320XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (320+k) (sourceBlock320PiPairs.getD k (0,0))
    (sourceEtaBatch320Lower k, sourceEtaBatch320Upper k)
    (sourceBlock320TwoPairs.getD k (0,0))

theorem sourceBlock320Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock320XiPair k).1:ℝ) ≤ (xi (xiGridArgument (320+k):ℂ)).re ∧
      (xi (xiGridArgument (320+k):ℂ)).re ≤ ((sourceBlock320XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (320+k) _ _ _
    (sourceBlock320PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch320_actual_enclosure k hk)
    (sourceBlock320TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock320Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock320XiPair k).1 := by
  decide +kernel

theorem sourceBlock320Reciprocal_check : ∀ k : Fin 32,
    sourceBlock320Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock320XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock320XiPair k)).2 ≤
      sourceBlock320Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block320_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((320+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (320+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock320Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (320+k) (sourceBlock320XiPair k) _
    (sourceBlock320Xi_enclosure k hk) (sourceBlock320Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock320Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first352_bound (k : ℕ) (hk : k < 352) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 320
  · exact sourceRoundedMidpoint_first320_bound k h
  · have hsum : 320+(k-320) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block320_bound (k-320) (by omega)

end ReciprocalXi
