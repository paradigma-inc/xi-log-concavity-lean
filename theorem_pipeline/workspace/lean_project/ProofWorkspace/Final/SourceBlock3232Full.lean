import ProofWorkspace.Final.SourceBlock3200Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3232DataFull
import ProofWorkspace.Final.EtaBlock3232Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3232XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3232+k) (sourceBlock3232PiPairs.getD k (0,0))
    (sourceEtaBatch3232Lower k, sourceEtaBatch3232Upper k)
    (sourceBlock3232TwoPairs.getD k (0,0))

theorem sourceBlock3232Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3232XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3232+k):ℂ)).re ∧
      (xi (xiGridArgument (3232+k):ℂ)).re ≤ ((sourceBlock3232XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3232+k) _ _ _
    (sourceBlock3232PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3232_actual_enclosure k hk)
    (sourceBlock3232TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3232Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3232XiPair k).1 := by
  decide +kernel

theorem sourceBlock3232Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3232Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3232XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3232XiPair k)).2 ≤
      sourceBlock3232Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3232_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3232+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3232+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3232Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3232+k) (sourceBlock3232XiPair k) _
    (sourceBlock3232Xi_enclosure k hk) (sourceBlock3232Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3232Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3264_bound (k : ℕ) (hk : k < 3264) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3232
  · exact sourceRoundedMidpoint_first3232_bound k h
  · have hsum : 3232+(k-3232) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3232_bound (k-3232) (by omega)

end ReciprocalXi
