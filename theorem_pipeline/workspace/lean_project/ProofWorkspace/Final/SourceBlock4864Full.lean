import ProofWorkspace.Final.SourceBlock4832Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4864DataFull
import ProofWorkspace.Final.EtaBlock4864Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4864XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4864+k) (sourceBlock4864PiPairs.getD k (0,0))
    (sourceEtaBatch4864Lower k, sourceEtaBatch4864Upper k)
    (sourceBlock4864TwoPairs.getD k (0,0))

theorem sourceBlock4864Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4864XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4864+k):ℂ)).re ∧
      (xi (xiGridArgument (4864+k):ℂ)).re ≤ ((sourceBlock4864XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4864+k) _ _ _
    (sourceBlock4864PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4864_actual_enclosure k hk)
    (sourceBlock4864TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4864Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4864XiPair k).1 := by
  decide +kernel

theorem sourceBlock4864Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4864Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4864XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4864XiPair k)).2 ≤
      sourceBlock4864Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4864_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4864+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4864+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4864Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4864+k) (sourceBlock4864XiPair k) _
    (sourceBlock4864Xi_enclosure k hk) (sourceBlock4864Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4864Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4896_bound (k : ℕ) (hk : k < 4896) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4864
  · exact sourceRoundedMidpoint_first4864_bound k h
  · have hsum : 4864+(k-4864) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4864_bound (k-4864) (by omega)

end ReciprocalXi
