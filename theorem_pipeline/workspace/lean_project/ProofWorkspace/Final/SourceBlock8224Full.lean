import ProofWorkspace.Final.SourceBlock8192Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8224DataFull
import ProofWorkspace.Final.EtaBlock8224Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8224XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8224+k) (sourceBlock8224PiPairs.getD k (0,0))
    (sourceEtaBatch8224Lower k, sourceEtaBatch8224Upper k)
    (sourceBlock8224TwoPairs.getD k (0,0))

theorem sourceBlock8224Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8224XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8224+k):ℂ)).re ∧
      (xi (xiGridArgument (8224+k):ℂ)).re ≤ ((sourceBlock8224XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8224+k) _ _ _
    (sourceBlock8224PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8224_actual_enclosure k hk)
    (sourceBlock8224TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8224Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8224XiPair k).1 := by
  decide +kernel

theorem sourceBlock8224Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8224Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8224XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8224XiPair k)).2 ≤
      sourceBlock8224Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8224_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8224+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8224+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8224Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8224+k) (sourceBlock8224XiPair k) _
    (sourceBlock8224Xi_enclosure k hk) (sourceBlock8224Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8224Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8256_bound (k : ℕ) (hk : k < 8256) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8224
  · exact sourceRoundedMidpoint_first8224_bound k h
  · have hsum : 8224+(k-8224) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8224_bound (k-8224) (by omega)

end ReciprocalXi
