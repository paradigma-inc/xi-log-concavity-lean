import ProofWorkspace.Final.SourceBlock6752Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6784DataFull
import ProofWorkspace.Final.EtaBlock6784Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6784XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6784+k) (sourceBlock6784PiPairs.getD k (0,0))
    (sourceEtaBatch6784Lower k, sourceEtaBatch6784Upper k)
    (sourceBlock6784TwoPairs.getD k (0,0))

theorem sourceBlock6784Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6784XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6784+k):ℂ)).re ∧
      (xi (xiGridArgument (6784+k):ℂ)).re ≤ ((sourceBlock6784XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6784+k) _ _ _
    (sourceBlock6784PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6784_actual_enclosure k hk)
    (sourceBlock6784TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6784Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6784XiPair k).1 := by
  decide +kernel

theorem sourceBlock6784Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6784Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6784XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6784XiPair k)).2 ≤
      sourceBlock6784Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6784_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6784+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6784+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6784Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6784+k) (sourceBlock6784XiPair k) _
    (sourceBlock6784Xi_enclosure k hk) (sourceBlock6784Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6784Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6816_bound (k : ℕ) (hk : k < 6816) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6784
  · exact sourceRoundedMidpoint_first6784_bound k h
  · have hsum : 6784+(k-6784) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6784_bound (k-6784) (by omega)

end ReciprocalXi
