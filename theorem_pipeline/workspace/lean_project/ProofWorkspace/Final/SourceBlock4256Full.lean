import ProofWorkspace.Final.SourceBlock4224Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4256DataFull
import ProofWorkspace.Final.EtaBlock4256Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4256XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4256+k) (sourceBlock4256PiPairs.getD k (0,0))
    (sourceEtaBatch4256Lower k, sourceEtaBatch4256Upper k)
    (sourceBlock4256TwoPairs.getD k (0,0))

theorem sourceBlock4256Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4256XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4256+k):ℂ)).re ∧
      (xi (xiGridArgument (4256+k):ℂ)).re ≤ ((sourceBlock4256XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4256+k) _ _ _
    (sourceBlock4256PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4256_actual_enclosure k hk)
    (sourceBlock4256TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4256Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4256XiPair k).1 := by
  decide +kernel

theorem sourceBlock4256Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4256Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4256XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4256XiPair k)).2 ≤
      sourceBlock4256Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4256_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4256+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4256+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4256Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4256+k) (sourceBlock4256XiPair k) _
    (sourceBlock4256Xi_enclosure k hk) (sourceBlock4256Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4256Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4288_bound (k : ℕ) (hk : k < 4288) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4256
  · exact sourceRoundedMidpoint_first4256_bound k h
  · have hsum : 4256+(k-4256) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4256_bound (k-4256) (by omega)

end ReciprocalXi
