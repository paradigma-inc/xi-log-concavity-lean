import ProofWorkspace.Final.SourceBlock4192Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4224DataFull
import ProofWorkspace.Final.EtaBlock4224Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4224XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4224+k) (sourceBlock4224PiPairs.getD k (0,0))
    (sourceEtaBatch4224Lower k, sourceEtaBatch4224Upper k)
    (sourceBlock4224TwoPairs.getD k (0,0))

theorem sourceBlock4224Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4224XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4224+k):ℂ)).re ∧
      (xi (xiGridArgument (4224+k):ℂ)).re ≤ ((sourceBlock4224XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4224+k) _ _ _
    (sourceBlock4224PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4224_actual_enclosure k hk)
    (sourceBlock4224TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4224Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4224XiPair k).1 := by
  decide +kernel

theorem sourceBlock4224Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4224Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4224XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4224XiPair k)).2 ≤
      sourceBlock4224Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4224_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4224+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4224+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4224Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4224+k) (sourceBlock4224XiPair k) _
    (sourceBlock4224Xi_enclosure k hk) (sourceBlock4224Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4224Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4256_bound (k : ℕ) (hk : k < 4256) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4224
  · exact sourceRoundedMidpoint_first4224_bound k h
  · have hsum : 4224+(k-4224) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4224_bound (k-4224) (by omega)

end ReciprocalXi
