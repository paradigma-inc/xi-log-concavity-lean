import ProofWorkspace.Final.SourceBlock6272Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6304DataFull
import ProofWorkspace.Final.EtaBlock6304Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6304XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6304+k) (sourceBlock6304PiPairs.getD k (0,0))
    (sourceEtaBatch6304Lower k, sourceEtaBatch6304Upper k)
    (sourceBlock6304TwoPairs.getD k (0,0))

theorem sourceBlock6304Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6304XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6304+k):ℂ)).re ∧
      (xi (xiGridArgument (6304+k):ℂ)).re ≤ ((sourceBlock6304XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6304+k) _ _ _
    (sourceBlock6304PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6304_actual_enclosure k hk)
    (sourceBlock6304TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6304Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6304XiPair k).1 := by
  decide +kernel

theorem sourceBlock6304Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6304Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6304XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6304XiPair k)).2 ≤
      sourceBlock6304Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6304_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6304+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6304+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6304Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6304+k) (sourceBlock6304XiPair k) _
    (sourceBlock6304Xi_enclosure k hk) (sourceBlock6304Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6304Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6336_bound (k : ℕ) (hk : k < 6336) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6304
  · exact sourceRoundedMidpoint_first6304_bound k h
  · have hsum : 6304+(k-6304) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6304_bound (k-6304) (by omega)

end ReciprocalXi
