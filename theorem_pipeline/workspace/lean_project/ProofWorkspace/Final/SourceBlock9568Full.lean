import ProofWorkspace.Final.SourceBlock9536Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9568DataFull
import ProofWorkspace.Final.EtaBlock9568Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9568XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9568+k) (sourceBlock9568PiPairs.getD k (0,0))
    (sourceEtaBatch9568Lower k, sourceEtaBatch9568Upper k)
    (sourceBlock9568TwoPairs.getD k (0,0))

theorem sourceBlock9568Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9568XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9568+k):ℂ)).re ∧
      (xi (xiGridArgument (9568+k):ℂ)).re ≤ ((sourceBlock9568XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9568+k) _ _ _
    (sourceBlock9568PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9568_actual_enclosure k hk)
    (sourceBlock9568TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9568Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9568XiPair k).1 := by
  decide +kernel

theorem sourceBlock9568Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9568Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9568XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9568XiPair k)).2 ≤
      sourceBlock9568Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9568_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9568+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9568+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9568Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9568+k) (sourceBlock9568XiPair k) _
    (sourceBlock9568Xi_enclosure k hk) (sourceBlock9568Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9568Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9600_bound (k : ℕ) (hk : k < 9600) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9568
  · exact sourceRoundedMidpoint_first9568_bound k h
  · have hsum : 9568+(k-9568) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9568_bound (k-9568) (by omega)

end ReciprocalXi
