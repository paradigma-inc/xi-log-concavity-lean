import ProofWorkspace.Final.SourceBlock13184Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13216DataFull
import ProofWorkspace.Final.EtaBlock13216Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13216XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13216+k) (sourceBlock13216PiPairs.getD k (0,0))
    (sourceEtaBatch13216Lower k, sourceEtaBatch13216Upper k)
    (sourceBlock13216TwoPairs.getD k (0,0))

theorem sourceBlock13216Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13216XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13216+k):ℂ)).re ∧
      (xi (xiGridArgument (13216+k):ℂ)).re ≤ ((sourceBlock13216XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13216+k) _ _ _
    (sourceBlock13216PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13216_actual_enclosure k hk)
    (sourceBlock13216TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13216Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13216XiPair k).1 := by
  decide +kernel

theorem sourceBlock13216Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13216Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13216XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13216XiPair k)).2 ≤
      sourceBlock13216Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13216_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13216+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13216+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13216Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13216+k) (sourceBlock13216XiPair k) _
    (sourceBlock13216Xi_enclosure k hk) (sourceBlock13216Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13216Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13248_bound (k : ℕ) (hk : k < 13248) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13216
  · exact sourceRoundedMidpoint_first13216_bound k h
  · have hsum : 13216+(k-13216) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13216_bound (k-13216) (by omega)

end ReciprocalXi
