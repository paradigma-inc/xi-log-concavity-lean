import ProofWorkspace.Final.SourceBlock3168Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3200DataFull
import ProofWorkspace.Final.EtaBlock3200Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3200XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3200+k) (sourceBlock3200PiPairs.getD k (0,0))
    (sourceEtaBatch3200Lower k, sourceEtaBatch3200Upper k)
    (sourceBlock3200TwoPairs.getD k (0,0))

theorem sourceBlock3200Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3200XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3200+k):ℂ)).re ∧
      (xi (xiGridArgument (3200+k):ℂ)).re ≤ ((sourceBlock3200XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3200+k) _ _ _
    (sourceBlock3200PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3200_actual_enclosure k hk)
    (sourceBlock3200TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3200Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3200XiPair k).1 := by
  decide +kernel

theorem sourceBlock3200Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3200Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3200XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3200XiPair k)).2 ≤
      sourceBlock3200Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3200_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3200+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3200+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3200Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3200+k) (sourceBlock3200XiPair k) _
    (sourceBlock3200Xi_enclosure k hk) (sourceBlock3200Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3200Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3232_bound (k : ℕ) (hk : k < 3232) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3200
  · exact sourceRoundedMidpoint_first3200_bound k h
  · have hsum : 3200+(k-3200) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3200_bound (k-3200) (by omega)

end ReciprocalXi
