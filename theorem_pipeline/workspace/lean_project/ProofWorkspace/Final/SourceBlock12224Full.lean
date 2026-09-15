import ProofWorkspace.Final.SourceBlock12192Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12224DataFull
import ProofWorkspace.Final.EtaBlock12224Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12224XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12224+k) (sourceBlock12224PiPairs.getD k (0,0))
    (sourceEtaBatch12224Lower k, sourceEtaBatch12224Upper k)
    (sourceBlock12224TwoPairs.getD k (0,0))

theorem sourceBlock12224Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12224XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12224+k):ℂ)).re ∧
      (xi (xiGridArgument (12224+k):ℂ)).re ≤ ((sourceBlock12224XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12224+k) _ _ _
    (sourceBlock12224PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12224_actual_enclosure k hk)
    (sourceBlock12224TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12224Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12224XiPair k).1 := by
  decide +kernel

theorem sourceBlock12224Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12224Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12224XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12224XiPair k)).2 ≤
      sourceBlock12224Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12224_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12224+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12224+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12224Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12224+k) (sourceBlock12224XiPair k) _
    (sourceBlock12224Xi_enclosure k hk) (sourceBlock12224Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12224Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12256_bound (k : ℕ) (hk : k < 12256) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12224
  · exact sourceRoundedMidpoint_first12224_bound k h
  · have hsum : 12224+(k-12224) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12224_bound (k-12224) (by omega)

end ReciprocalXi
