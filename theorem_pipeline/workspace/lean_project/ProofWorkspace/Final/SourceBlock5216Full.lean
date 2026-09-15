import ProofWorkspace.Final.SourceBlock5184Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5216DataFull
import ProofWorkspace.Final.EtaBlock5216Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5216XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5216+k) (sourceBlock5216PiPairs.getD k (0,0))
    (sourceEtaBatch5216Lower k, sourceEtaBatch5216Upper k)
    (sourceBlock5216TwoPairs.getD k (0,0))

theorem sourceBlock5216Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5216XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5216+k):ℂ)).re ∧
      (xi (xiGridArgument (5216+k):ℂ)).re ≤ ((sourceBlock5216XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5216+k) _ _ _
    (sourceBlock5216PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5216_actual_enclosure k hk)
    (sourceBlock5216TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5216Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5216XiPair k).1 := by
  decide +kernel

theorem sourceBlock5216Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5216Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5216XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5216XiPair k)).2 ≤
      sourceBlock5216Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5216_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5216+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5216+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5216Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5216+k) (sourceBlock5216XiPair k) _
    (sourceBlock5216Xi_enclosure k hk) (sourceBlock5216Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5216Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5248_bound (k : ℕ) (hk : k < 5248) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5216
  · exact sourceRoundedMidpoint_first5216_bound k h
  · have hsum : 5216+(k-5216) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5216_bound (k-5216) (by omega)

end ReciprocalXi
