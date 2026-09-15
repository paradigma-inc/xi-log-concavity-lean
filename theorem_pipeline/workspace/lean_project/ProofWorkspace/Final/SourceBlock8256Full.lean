import ProofWorkspace.Final.SourceBlock8224Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8256DataFull
import ProofWorkspace.Final.EtaBlock8256Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8256XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8256+k) (sourceBlock8256PiPairs.getD k (0,0))
    (sourceEtaBatch8256Lower k, sourceEtaBatch8256Upper k)
    (sourceBlock8256TwoPairs.getD k (0,0))

theorem sourceBlock8256Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8256XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8256+k):ℂ)).re ∧
      (xi (xiGridArgument (8256+k):ℂ)).re ≤ ((sourceBlock8256XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8256+k) _ _ _
    (sourceBlock8256PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8256_actual_enclosure k hk)
    (sourceBlock8256TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8256Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8256XiPair k).1 := by
  decide +kernel

theorem sourceBlock8256Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8256Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8256XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8256XiPair k)).2 ≤
      sourceBlock8256Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8256_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8256+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8256+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8256Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8256+k) (sourceBlock8256XiPair k) _
    (sourceBlock8256Xi_enclosure k hk) (sourceBlock8256Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8256Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8288_bound (k : ℕ) (hk : k < 8288) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8256
  · exact sourceRoundedMidpoint_first8256_bound k h
  · have hsum : 8256+(k-8256) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8256_bound (k-8256) (by omega)

end ReciprocalXi
