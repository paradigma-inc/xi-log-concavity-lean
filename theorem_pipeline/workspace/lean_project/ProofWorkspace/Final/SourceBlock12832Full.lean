import ProofWorkspace.Final.SourceBlock12800Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12832DataFull
import ProofWorkspace.Final.EtaBlock12832Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12832XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12832+k) (sourceBlock12832PiPairs.getD k (0,0))
    (sourceEtaBatch12832Lower k, sourceEtaBatch12832Upper k)
    (sourceBlock12832TwoPairs.getD k (0,0))

theorem sourceBlock12832Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12832XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12832+k):ℂ)).re ∧
      (xi (xiGridArgument (12832+k):ℂ)).re ≤ ((sourceBlock12832XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12832+k) _ _ _
    (sourceBlock12832PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12832_actual_enclosure k hk)
    (sourceBlock12832TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12832Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12832XiPair k).1 := by
  decide +kernel

theorem sourceBlock12832Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12832Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12832XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12832XiPair k)).2 ≤
      sourceBlock12832Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12832_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12832+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12832+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12832Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12832+k) (sourceBlock12832XiPair k) _
    (sourceBlock12832Xi_enclosure k hk) (sourceBlock12832Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12832Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12864_bound (k : ℕ) (hk : k < 12864) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12832
  · exact sourceRoundedMidpoint_first12832_bound k h
  · have hsum : 12832+(k-12832) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12832_bound (k-12832) (by omega)

end ReciprocalXi
