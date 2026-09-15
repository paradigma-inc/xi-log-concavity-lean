import ProofWorkspace.Final.SourceBlock10112Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10144DataFull
import ProofWorkspace.Final.EtaBlock10144Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10144XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10144+k) (sourceBlock10144PiPairs.getD k (0,0))
    (sourceEtaBatch10144Lower k, sourceEtaBatch10144Upper k)
    (sourceBlock10144TwoPairs.getD k (0,0))

theorem sourceBlock10144Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10144XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10144+k):ℂ)).re ∧
      (xi (xiGridArgument (10144+k):ℂ)).re ≤ ((sourceBlock10144XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10144+k) _ _ _
    (sourceBlock10144PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10144_actual_enclosure k hk)
    (sourceBlock10144TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10144Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10144XiPair k).1 := by
  decide +kernel

theorem sourceBlock10144Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10144Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10144XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10144XiPair k)).2 ≤
      sourceBlock10144Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10144_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10144+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10144+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10144Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10144+k) (sourceBlock10144XiPair k) _
    (sourceBlock10144Xi_enclosure k hk) (sourceBlock10144Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10144Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10176_bound (k : ℕ) (hk : k < 10176) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10144
  · exact sourceRoundedMidpoint_first10144_bound k h
  · have hsum : 10144+(k-10144) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10144_bound (k-10144) (by omega)

end ReciprocalXi
