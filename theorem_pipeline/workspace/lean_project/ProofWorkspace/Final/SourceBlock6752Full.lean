import ProofWorkspace.Final.SourceBlock6720Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6752DataFull
import ProofWorkspace.Final.EtaBlock6752Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6752XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6752+k) (sourceBlock6752PiPairs.getD k (0,0))
    (sourceEtaBatch6752Lower k, sourceEtaBatch6752Upper k)
    (sourceBlock6752TwoPairs.getD k (0,0))

theorem sourceBlock6752Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6752XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6752+k):ℂ)).re ∧
      (xi (xiGridArgument (6752+k):ℂ)).re ≤ ((sourceBlock6752XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6752+k) _ _ _
    (sourceBlock6752PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6752_actual_enclosure k hk)
    (sourceBlock6752TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6752Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6752XiPair k).1 := by
  decide +kernel

theorem sourceBlock6752Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6752Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6752XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6752XiPair k)).2 ≤
      sourceBlock6752Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6752_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6752+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6752+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6752Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6752+k) (sourceBlock6752XiPair k) _
    (sourceBlock6752Xi_enclosure k hk) (sourceBlock6752Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6752Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6784_bound (k : ℕ) (hk : k < 6784) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6752
  · exact sourceRoundedMidpoint_first6752_bound k h
  · have hsum : 6752+(k-6752) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6752_bound (k-6752) (by omega)

end ReciprocalXi
