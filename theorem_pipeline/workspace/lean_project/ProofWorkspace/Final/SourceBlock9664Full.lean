import ProofWorkspace.Final.SourceBlock9632Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9664DataFull
import ProofWorkspace.Final.EtaBlock9664Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9664XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9664+k) (sourceBlock9664PiPairs.getD k (0,0))
    (sourceEtaBatch9664Lower k, sourceEtaBatch9664Upper k)
    (sourceBlock9664TwoPairs.getD k (0,0))

theorem sourceBlock9664Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9664XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9664+k):ℂ)).re ∧
      (xi (xiGridArgument (9664+k):ℂ)).re ≤ ((sourceBlock9664XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9664+k) _ _ _
    (sourceBlock9664PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9664_actual_enclosure k hk)
    (sourceBlock9664TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9664Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9664XiPair k).1 := by
  decide +kernel

theorem sourceBlock9664Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9664Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9664XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9664XiPair k)).2 ≤
      sourceBlock9664Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9664_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9664+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9664+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9664Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9664+k) (sourceBlock9664XiPair k) _
    (sourceBlock9664Xi_enclosure k hk) (sourceBlock9664Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9664Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9696_bound (k : ℕ) (hk : k < 9696) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9664
  · exact sourceRoundedMidpoint_first9664_bound k h
  · have hsum : 9664+(k-9664) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9664_bound (k-9664) (by omega)

end ReciprocalXi
