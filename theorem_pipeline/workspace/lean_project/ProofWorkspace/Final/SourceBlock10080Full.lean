import ProofWorkspace.Final.SourceBlock10048Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10080DataFull
import ProofWorkspace.Final.EtaBlock10080Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10080XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10080+k) (sourceBlock10080PiPairs.getD k (0,0))
    (sourceEtaBatch10080Lower k, sourceEtaBatch10080Upper k)
    (sourceBlock10080TwoPairs.getD k (0,0))

theorem sourceBlock10080Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10080XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10080+k):ℂ)).re ∧
      (xi (xiGridArgument (10080+k):ℂ)).re ≤ ((sourceBlock10080XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10080+k) _ _ _
    (sourceBlock10080PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10080_actual_enclosure k hk)
    (sourceBlock10080TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10080Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10080XiPair k).1 := by
  decide +kernel

theorem sourceBlock10080Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10080Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10080XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10080XiPair k)).2 ≤
      sourceBlock10080Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10080_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10080+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10080+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10080Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10080+k) (sourceBlock10080XiPair k) _
    (sourceBlock10080Xi_enclosure k hk) (sourceBlock10080Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10080Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10112_bound (k : ℕ) (hk : k < 10112) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10080
  · exact sourceRoundedMidpoint_first10080_bound k h
  · have hsum : 10080+(k-10080) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10080_bound (k-10080) (by omega)

end ReciprocalXi
