import ProofWorkspace.Final.SourceBlock6688Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6720DataFull
import ProofWorkspace.Final.EtaBlock6720Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6720XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6720+k) (sourceBlock6720PiPairs.getD k (0,0))
    (sourceEtaBatch6720Lower k, sourceEtaBatch6720Upper k)
    (sourceBlock6720TwoPairs.getD k (0,0))

theorem sourceBlock6720Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6720XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6720+k):ℂ)).re ∧
      (xi (xiGridArgument (6720+k):ℂ)).re ≤ ((sourceBlock6720XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6720+k) _ _ _
    (sourceBlock6720PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6720_actual_enclosure k hk)
    (sourceBlock6720TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6720Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6720XiPair k).1 := by
  decide +kernel

theorem sourceBlock6720Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6720Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6720XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6720XiPair k)).2 ≤
      sourceBlock6720Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6720_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6720+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6720+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6720Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6720+k) (sourceBlock6720XiPair k) _
    (sourceBlock6720Xi_enclosure k hk) (sourceBlock6720Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6720Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6752_bound (k : ℕ) (hk : k < 6752) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6720
  · exact sourceRoundedMidpoint_first6720_bound k h
  · have hsum : 6720+(k-6720) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6720_bound (k-6720) (by omega)

end ReciprocalXi
