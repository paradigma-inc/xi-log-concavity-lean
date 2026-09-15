import ProofWorkspace.Final.SourceBlock3648Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3680DataFull
import ProofWorkspace.Final.EtaBlock3680Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3680XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3680+k) (sourceBlock3680PiPairs.getD k (0,0))
    (sourceEtaBatch3680Lower k, sourceEtaBatch3680Upper k)
    (sourceBlock3680TwoPairs.getD k (0,0))

theorem sourceBlock3680Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3680XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3680+k):ℂ)).re ∧
      (xi (xiGridArgument (3680+k):ℂ)).re ≤ ((sourceBlock3680XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3680+k) _ _ _
    (sourceBlock3680PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3680_actual_enclosure k hk)
    (sourceBlock3680TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3680Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3680XiPair k).1 := by
  decide +kernel

theorem sourceBlock3680Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3680Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3680XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3680XiPair k)).2 ≤
      sourceBlock3680Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3680_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3680+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3680+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3680Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3680+k) (sourceBlock3680XiPair k) _
    (sourceBlock3680Xi_enclosure k hk) (sourceBlock3680Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3680Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3712_bound (k : ℕ) (hk : k < 3712) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3680
  · exact sourceRoundedMidpoint_first3680_bound k h
  · have hsum : 3680+(k-3680) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3680_bound (k-3680) (by omega)

end ReciprocalXi
