import ProofWorkspace.Final.SourceBlock2720Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2752DataFull
import ProofWorkspace.Final.EtaBlock2752Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2752XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2752+k) (sourceBlock2752PiPairs.getD k (0,0))
    (sourceEtaBatch2752Lower k, sourceEtaBatch2752Upper k)
    (sourceBlock2752TwoPairs.getD k (0,0))

theorem sourceBlock2752Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2752XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2752+k):ℂ)).re ∧
      (xi (xiGridArgument (2752+k):ℂ)).re ≤ ((sourceBlock2752XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2752+k) _ _ _
    (sourceBlock2752PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2752_actual_enclosure k hk)
    (sourceBlock2752TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2752Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2752XiPair k).1 := by
  decide +kernel

theorem sourceBlock2752Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2752Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2752XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2752XiPair k)).2 ≤
      sourceBlock2752Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2752_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2752+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2752+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2752Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2752+k) (sourceBlock2752XiPair k) _
    (sourceBlock2752Xi_enclosure k hk) (sourceBlock2752Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2752Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2784_bound (k : ℕ) (hk : k < 2784) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2752
  · exact sourceRoundedMidpoint_first2752_bound k h
  · have hsum : 2752+(k-2752) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2752_bound (k-2752) (by omega)

end ReciprocalXi
