import ProofWorkspace.Final.SourceBlock224Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock256DataFull
import ProofWorkspace.Final.EtaBlock256Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock256XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (256+k) (sourceBlock256PiPairs.getD k (0,0))
    (sourceEtaBatch256Lower k, sourceEtaBatch256Upper k)
    (sourceBlock256TwoPairs.getD k (0,0))

theorem sourceBlock256Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock256XiPair k).1:ℝ) ≤ (xi (xiGridArgument (256+k):ℂ)).re ∧
      (xi (xiGridArgument (256+k):ℂ)).re ≤ ((sourceBlock256XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (256+k) _ _ _
    (sourceBlock256PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch256_actual_enclosure k hk)
    (sourceBlock256TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock256Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock256XiPair k).1 := by
  decide +kernel

theorem sourceBlock256Reciprocal_check : ∀ k : Fin 32,
    sourceBlock256Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock256XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock256XiPair k)).2 ≤
      sourceBlock256Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block256_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((256+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (256+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock256Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (256+k) (sourceBlock256XiPair k) _
    (sourceBlock256Xi_enclosure k hk) (sourceBlock256Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock256Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first288_bound (k : ℕ) (hk : k < 288) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 256
  · exact sourceRoundedMidpoint_first256_bound k h
  · have hsum : 256+(k-256) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block256_bound (k-256) (by omega)

end ReciprocalXi
