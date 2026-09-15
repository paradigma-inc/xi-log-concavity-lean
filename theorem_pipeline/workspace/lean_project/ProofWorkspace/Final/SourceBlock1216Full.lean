import ProofWorkspace.Final.SourceBlock1184Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1216DataFull
import ProofWorkspace.Final.EtaBlock1216Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1216XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1216+k) (sourceBlock1216PiPairs.getD k (0,0))
    (sourceEtaBatch1216Lower k, sourceEtaBatch1216Upper k)
    (sourceBlock1216TwoPairs.getD k (0,0))

theorem sourceBlock1216Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1216XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1216+k):ℂ)).re ∧
      (xi (xiGridArgument (1216+k):ℂ)).re ≤ ((sourceBlock1216XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1216+k) _ _ _
    (sourceBlock1216PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1216_actual_enclosure k hk)
    (sourceBlock1216TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1216Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1216XiPair k).1 := by
  decide +kernel

theorem sourceBlock1216Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1216Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1216XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1216XiPair k)).2 ≤
      sourceBlock1216Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1216_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1216+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1216+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1216Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1216+k) (sourceBlock1216XiPair k) _
    (sourceBlock1216Xi_enclosure k hk) (sourceBlock1216Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1216Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1248_bound (k : ℕ) (hk : k < 1248) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1216
  · exact sourceRoundedMidpoint_first1216_bound k h
  · have hsum : 1216+(k-1216) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1216_bound (k-1216) (by omega)

end ReciprocalXi
