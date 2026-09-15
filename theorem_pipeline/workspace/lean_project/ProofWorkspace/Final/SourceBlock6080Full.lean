import ProofWorkspace.Final.SourceBlock6048Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6080DataFull
import ProofWorkspace.Final.EtaBlock6080Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6080XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6080+k) (sourceBlock6080PiPairs.getD k (0,0))
    (sourceEtaBatch6080Lower k, sourceEtaBatch6080Upper k)
    (sourceBlock6080TwoPairs.getD k (0,0))

theorem sourceBlock6080Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6080XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6080+k):ℂ)).re ∧
      (xi (xiGridArgument (6080+k):ℂ)).re ≤ ((sourceBlock6080XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6080+k) _ _ _
    (sourceBlock6080PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6080_actual_enclosure k hk)
    (sourceBlock6080TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6080Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6080XiPair k).1 := by
  decide +kernel

theorem sourceBlock6080Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6080Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6080XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6080XiPair k)).2 ≤
      sourceBlock6080Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6080_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6080+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6080+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6080Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6080+k) (sourceBlock6080XiPair k) _
    (sourceBlock6080Xi_enclosure k hk) (sourceBlock6080Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6080Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6112_bound (k : ℕ) (hk : k < 6112) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6080
  · exact sourceRoundedMidpoint_first6080_bound k h
  · have hsum : 6080+(k-6080) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6080_bound (k-6080) (by omega)

end ReciprocalXi
