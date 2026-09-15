import ProofWorkspace.Final.SourceBlock2784Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2816DataFull
import ProofWorkspace.Final.EtaBlock2816Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2816XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2816+k) (sourceBlock2816PiPairs.getD k (0,0))
    (sourceEtaBatch2816Lower k, sourceEtaBatch2816Upper k)
    (sourceBlock2816TwoPairs.getD k (0,0))

theorem sourceBlock2816Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2816XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2816+k):ℂ)).re ∧
      (xi (xiGridArgument (2816+k):ℂ)).re ≤ ((sourceBlock2816XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2816+k) _ _ _
    (sourceBlock2816PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2816_actual_enclosure k hk)
    (sourceBlock2816TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2816Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2816XiPair k).1 := by
  decide +kernel

theorem sourceBlock2816Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2816Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2816XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2816XiPair k)).2 ≤
      sourceBlock2816Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2816_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2816+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2816+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2816Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2816+k) (sourceBlock2816XiPair k) _
    (sourceBlock2816Xi_enclosure k hk) (sourceBlock2816Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2816Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2848_bound (k : ℕ) (hk : k < 2848) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2816
  · exact sourceRoundedMidpoint_first2816_bound k h
  · have hsum : 2816+(k-2816) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2816_bound (k-2816) (by omega)

end ReciprocalXi
