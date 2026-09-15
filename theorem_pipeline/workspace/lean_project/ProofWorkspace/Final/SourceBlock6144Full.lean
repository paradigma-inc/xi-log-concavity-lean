import ProofWorkspace.Final.SourceBlock6112Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6144DataFull
import ProofWorkspace.Final.EtaBlock6144Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6144XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6144+k) (sourceBlock6144PiPairs.getD k (0,0))
    (sourceEtaBatch6144Lower k, sourceEtaBatch6144Upper k)
    (sourceBlock6144TwoPairs.getD k (0,0))

theorem sourceBlock6144Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6144XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6144+k):ℂ)).re ∧
      (xi (xiGridArgument (6144+k):ℂ)).re ≤ ((sourceBlock6144XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6144+k) _ _ _
    (sourceBlock6144PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6144_actual_enclosure k hk)
    (sourceBlock6144TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6144Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6144XiPair k).1 := by
  decide +kernel

theorem sourceBlock6144Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6144Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6144XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6144XiPair k)).2 ≤
      sourceBlock6144Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6144_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6144+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6144+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6144Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6144+k) (sourceBlock6144XiPair k) _
    (sourceBlock6144Xi_enclosure k hk) (sourceBlock6144Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6144Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6176_bound (k : ℕ) (hk : k < 6176) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6144
  · exact sourceRoundedMidpoint_first6144_bound k h
  · have hsum : 6144+(k-6144) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6144_bound (k-6144) (by omega)

end ReciprocalXi
