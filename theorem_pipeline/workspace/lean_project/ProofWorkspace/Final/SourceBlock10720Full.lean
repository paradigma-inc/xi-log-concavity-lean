import ProofWorkspace.Final.SourceBlock10688Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10720DataFull
import ProofWorkspace.Final.EtaBlock10720Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10720XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10720+k) (sourceBlock10720PiPairs.getD k (0,0))
    (sourceEtaBatch10720Lower k, sourceEtaBatch10720Upper k)
    (sourceBlock10720TwoPairs.getD k (0,0))

theorem sourceBlock10720Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10720XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10720+k):ℂ)).re ∧
      (xi (xiGridArgument (10720+k):ℂ)).re ≤ ((sourceBlock10720XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10720+k) _ _ _
    (sourceBlock10720PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10720_actual_enclosure k hk)
    (sourceBlock10720TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10720Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10720XiPair k).1 := by
  decide +kernel

theorem sourceBlock10720Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10720Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10720XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10720XiPair k)).2 ≤
      sourceBlock10720Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10720_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10720+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10720+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10720Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10720+k) (sourceBlock10720XiPair k) _
    (sourceBlock10720Xi_enclosure k hk) (sourceBlock10720Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10720Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10752_bound (k : ℕ) (hk : k < 10752) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10720
  · exact sourceRoundedMidpoint_first10720_bound k h
  · have hsum : 10720+(k-10720) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10720_bound (k-10720) (by omega)

end ReciprocalXi
