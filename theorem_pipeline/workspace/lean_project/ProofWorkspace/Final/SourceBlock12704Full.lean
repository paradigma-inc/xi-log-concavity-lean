import ProofWorkspace.Final.SourceBlock12672Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12704DataFull
import ProofWorkspace.Final.EtaBlock12704Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12704XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12704+k) (sourceBlock12704PiPairs.getD k (0,0))
    (sourceEtaBatch12704Lower k, sourceEtaBatch12704Upper k)
    (sourceBlock12704TwoPairs.getD k (0,0))

theorem sourceBlock12704Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12704XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12704+k):ℂ)).re ∧
      (xi (xiGridArgument (12704+k):ℂ)).re ≤ ((sourceBlock12704XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12704+k) _ _ _
    (sourceBlock12704PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12704_actual_enclosure k hk)
    (sourceBlock12704TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12704Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12704XiPair k).1 := by
  decide +kernel

theorem sourceBlock12704Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12704Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12704XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12704XiPair k)).2 ≤
      sourceBlock12704Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12704_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12704+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12704+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12704Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12704+k) (sourceBlock12704XiPair k) _
    (sourceBlock12704Xi_enclosure k hk) (sourceBlock12704Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12704Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12736_bound (k : ℕ) (hk : k < 12736) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12704
  · exact sourceRoundedMidpoint_first12704_bound k h
  · have hsum : 12704+(k-12704) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12704_bound (k-12704) (by omega)

end ReciprocalXi
