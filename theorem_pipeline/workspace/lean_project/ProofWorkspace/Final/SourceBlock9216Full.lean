import ProofWorkspace.Final.SourceBlock9184Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9216DataFull
import ProofWorkspace.Final.EtaBlock9216Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9216XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9216+k) (sourceBlock9216PiPairs.getD k (0,0))
    (sourceEtaBatch9216Lower k, sourceEtaBatch9216Upper k)
    (sourceBlock9216TwoPairs.getD k (0,0))

theorem sourceBlock9216Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9216XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9216+k):ℂ)).re ∧
      (xi (xiGridArgument (9216+k):ℂ)).re ≤ ((sourceBlock9216XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9216+k) _ _ _
    (sourceBlock9216PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9216_actual_enclosure k hk)
    (sourceBlock9216TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9216Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9216XiPair k).1 := by
  decide +kernel

theorem sourceBlock9216Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9216Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9216XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9216XiPair k)).2 ≤
      sourceBlock9216Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9216_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9216+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9216+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9216Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9216+k) (sourceBlock9216XiPair k) _
    (sourceBlock9216Xi_enclosure k hk) (sourceBlock9216Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9216Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9248_bound (k : ℕ) (hk : k < 9248) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9216
  · exact sourceRoundedMidpoint_first9216_bound k h
  · have hsum : 9216+(k-9216) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9216_bound (k-9216) (by omega)

end ReciprocalXi
