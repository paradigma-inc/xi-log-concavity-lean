import ProofWorkspace.Final.SourceBlock12160Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12192DataFull
import ProofWorkspace.Final.EtaBlock12192Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12192XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12192+k) (sourceBlock12192PiPairs.getD k (0,0))
    (sourceEtaBatch12192Lower k, sourceEtaBatch12192Upper k)
    (sourceBlock12192TwoPairs.getD k (0,0))

theorem sourceBlock12192Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12192XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12192+k):ℂ)).re ∧
      (xi (xiGridArgument (12192+k):ℂ)).re ≤ ((sourceBlock12192XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12192+k) _ _ _
    (sourceBlock12192PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12192_actual_enclosure k hk)
    (sourceBlock12192TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12192Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12192XiPair k).1 := by
  decide +kernel

theorem sourceBlock12192Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12192Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12192XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12192XiPair k)).2 ≤
      sourceBlock12192Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12192_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12192+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12192+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12192Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12192+k) (sourceBlock12192XiPair k) _
    (sourceBlock12192Xi_enclosure k hk) (sourceBlock12192Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12192Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12224_bound (k : ℕ) (hk : k < 12224) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12192
  · exact sourceRoundedMidpoint_first12192_bound k h
  · have hsum : 12192+(k-12192) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12192_bound (k-12192) (by omega)

end ReciprocalXi
