import ProofWorkspace.Final.SourceBlock12224Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12256DataFull
import ProofWorkspace.Final.EtaBlock12256Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12256XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12256+k) (sourceBlock12256PiPairs.getD k (0,0))
    (sourceEtaBatch12256Lower k, sourceEtaBatch12256Upper k)
    (sourceBlock12256TwoPairs.getD k (0,0))

theorem sourceBlock12256Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12256XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12256+k):ℂ)).re ∧
      (xi (xiGridArgument (12256+k):ℂ)).re ≤ ((sourceBlock12256XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12256+k) _ _ _
    (sourceBlock12256PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12256_actual_enclosure k hk)
    (sourceBlock12256TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12256Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12256XiPair k).1 := by
  decide +kernel

theorem sourceBlock12256Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12256Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12256XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12256XiPair k)).2 ≤
      sourceBlock12256Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12256_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12256+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12256+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12256Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12256+k) (sourceBlock12256XiPair k) _
    (sourceBlock12256Xi_enclosure k hk) (sourceBlock12256Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12256Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12288_bound (k : ℕ) (hk : k < 12288) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12256
  · exact sourceRoundedMidpoint_first12256_bound k h
  · have hsum : 12256+(k-12256) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12256_bound (k-12256) (by omega)

end ReciprocalXi
