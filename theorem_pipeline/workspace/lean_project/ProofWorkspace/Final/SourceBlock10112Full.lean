import ProofWorkspace.Final.SourceBlock10080Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10112DataFull
import ProofWorkspace.Final.EtaBlock10112Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10112XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10112+k) (sourceBlock10112PiPairs.getD k (0,0))
    (sourceEtaBatch10112Lower k, sourceEtaBatch10112Upper k)
    (sourceBlock10112TwoPairs.getD k (0,0))

theorem sourceBlock10112Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10112XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10112+k):ℂ)).re ∧
      (xi (xiGridArgument (10112+k):ℂ)).re ≤ ((sourceBlock10112XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10112+k) _ _ _
    (sourceBlock10112PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10112_actual_enclosure k hk)
    (sourceBlock10112TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10112Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10112XiPair k).1 := by
  decide +kernel

theorem sourceBlock10112Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10112Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10112XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10112XiPair k)).2 ≤
      sourceBlock10112Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10112_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10112+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10112+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10112Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10112+k) (sourceBlock10112XiPair k) _
    (sourceBlock10112Xi_enclosure k hk) (sourceBlock10112Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10112Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10144_bound (k : ℕ) (hk : k < 10144) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10112
  · exact sourceRoundedMidpoint_first10112_bound k h
  · have hsum : 10112+(k-10112) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10112_bound (k-10112) (by omega)

end ReciprocalXi
