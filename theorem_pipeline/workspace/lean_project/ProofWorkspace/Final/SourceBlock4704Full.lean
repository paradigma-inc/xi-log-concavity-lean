import ProofWorkspace.Final.SourceBlock4672Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4704DataFull
import ProofWorkspace.Final.EtaBlock4704Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4704XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4704+k) (sourceBlock4704PiPairs.getD k (0,0))
    (sourceEtaBatch4704Lower k, sourceEtaBatch4704Upper k)
    (sourceBlock4704TwoPairs.getD k (0,0))

theorem sourceBlock4704Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4704XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4704+k):ℂ)).re ∧
      (xi (xiGridArgument (4704+k):ℂ)).re ≤ ((sourceBlock4704XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4704+k) _ _ _
    (sourceBlock4704PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4704_actual_enclosure k hk)
    (sourceBlock4704TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4704Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4704XiPair k).1 := by
  decide +kernel

theorem sourceBlock4704Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4704Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4704XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4704XiPair k)).2 ≤
      sourceBlock4704Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4704_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4704+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4704+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4704Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4704+k) (sourceBlock4704XiPair k) _
    (sourceBlock4704Xi_enclosure k hk) (sourceBlock4704Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4704Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4736_bound (k : ℕ) (hk : k < 4736) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4704
  · exact sourceRoundedMidpoint_first4704_bound k h
  · have hsum : 4704+(k-4704) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4704_bound (k-4704) (by omega)

end ReciprocalXi
