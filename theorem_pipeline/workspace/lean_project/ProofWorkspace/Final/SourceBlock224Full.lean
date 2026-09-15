import ProofWorkspace.Final.SourceBlock192Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock224DataFull
import ProofWorkspace.Final.EtaBlock224Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock224XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (224+k) (sourceBlock224PiPairs.getD k (0,0))
    (sourceEtaBatch224Lower k, sourceEtaBatch224Upper k)
    (sourceBlock224TwoPairs.getD k (0,0))

theorem sourceBlock224Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock224XiPair k).1:ℝ) ≤ (xi (xiGridArgument (224+k):ℂ)).re ∧
      (xi (xiGridArgument (224+k):ℂ)).re ≤ ((sourceBlock224XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (224+k) _ _ _
    (sourceBlock224PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch224_actual_enclosure k hk)
    (sourceBlock224TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock224Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock224XiPair k).1 := by
  decide +kernel

theorem sourceBlock224Reciprocal_check : ∀ k : Fin 32,
    sourceBlock224Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock224XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock224XiPair k)).2 ≤
      sourceBlock224Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block224_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((224+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (224+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock224Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (224+k) (sourceBlock224XiPair k) _
    (sourceBlock224Xi_enclosure k hk) (sourceBlock224Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock224Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first256_bound (k : ℕ) (hk : k < 256) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 224
  · exact sourceRoundedMidpoint_first224_bound k h
  · have hsum : 224+(k-224) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block224_bound (k-224) (by omega)

end ReciprocalXi
