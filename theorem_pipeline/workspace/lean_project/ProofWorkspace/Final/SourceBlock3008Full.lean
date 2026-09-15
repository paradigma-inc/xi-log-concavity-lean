import ProofWorkspace.Final.SourceBlock2976Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3008DataFull
import ProofWorkspace.Final.EtaBlock3008Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3008XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3008+k) (sourceBlock3008PiPairs.getD k (0,0))
    (sourceEtaBatch3008Lower k, sourceEtaBatch3008Upper k)
    (sourceBlock3008TwoPairs.getD k (0,0))

theorem sourceBlock3008Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3008XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3008+k):ℂ)).re ∧
      (xi (xiGridArgument (3008+k):ℂ)).re ≤ ((sourceBlock3008XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3008+k) _ _ _
    (sourceBlock3008PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3008_actual_enclosure k hk)
    (sourceBlock3008TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3008Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3008XiPair k).1 := by
  decide +kernel

theorem sourceBlock3008Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3008Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3008XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3008XiPair k)).2 ≤
      sourceBlock3008Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3008_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3008+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3008+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3008Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3008+k) (sourceBlock3008XiPair k) _
    (sourceBlock3008Xi_enclosure k hk) (sourceBlock3008Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3008Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3040_bound (k : ℕ) (hk : k < 3040) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3008
  · exact sourceRoundedMidpoint_first3008_bound k h
  · have hsum : 3008+(k-3008) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3008_bound (k-3008) (by omega)

end ReciprocalXi
