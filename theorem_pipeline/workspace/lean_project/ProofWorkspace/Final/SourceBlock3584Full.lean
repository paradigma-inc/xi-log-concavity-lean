import ProofWorkspace.Final.SourceBlock3552Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3584DataFull
import ProofWorkspace.Final.EtaBlock3584Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3584XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3584+k) (sourceBlock3584PiPairs.getD k (0,0))
    (sourceEtaBatch3584Lower k, sourceEtaBatch3584Upper k)
    (sourceBlock3584TwoPairs.getD k (0,0))

theorem sourceBlock3584Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3584XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3584+k):ℂ)).re ∧
      (xi (xiGridArgument (3584+k):ℂ)).re ≤ ((sourceBlock3584XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3584+k) _ _ _
    (sourceBlock3584PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3584_actual_enclosure k hk)
    (sourceBlock3584TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3584Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3584XiPair k).1 := by
  decide +kernel

theorem sourceBlock3584Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3584Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3584XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3584XiPair k)).2 ≤
      sourceBlock3584Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3584_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3584+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3584+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3584Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3584+k) (sourceBlock3584XiPair k) _
    (sourceBlock3584Xi_enclosure k hk) (sourceBlock3584Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3584Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3616_bound (k : ℕ) (hk : k < 3616) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3584
  · exact sourceRoundedMidpoint_first3584_bound k h
  · have hsum : 3584+(k-3584) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3584_bound (k-3584) (by omega)

end ReciprocalXi
