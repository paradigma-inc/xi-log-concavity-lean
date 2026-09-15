import ProofWorkspace.Final.SourceBlock672Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock704DataFull
import ProofWorkspace.Final.EtaBlock704Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock704XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (704+k) (sourceBlock704PiPairs.getD k (0,0))
    (sourceEtaBatch704Lower k, sourceEtaBatch704Upper k)
    (sourceBlock704TwoPairs.getD k (0,0))

theorem sourceBlock704Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock704XiPair k).1:ℝ) ≤ (xi (xiGridArgument (704+k):ℂ)).re ∧
      (xi (xiGridArgument (704+k):ℂ)).re ≤ ((sourceBlock704XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (704+k) _ _ _
    (sourceBlock704PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch704_actual_enclosure k hk)
    (sourceBlock704TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock704Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock704XiPair k).1 := by
  decide +kernel

theorem sourceBlock704Reciprocal_check : ∀ k : Fin 32,
    sourceBlock704Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock704XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock704XiPair k)).2 ≤
      sourceBlock704Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block704_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((704+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (704+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock704Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (704+k) (sourceBlock704XiPair k) _
    (sourceBlock704Xi_enclosure k hk) (sourceBlock704Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock704Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first736_bound (k : ℕ) (hk : k < 736) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 704
  · exact sourceRoundedMidpoint_first704_bound k h
  · have hsum : 704+(k-704) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block704_bound (k-704) (by omega)

end ReciprocalXi
