import ProofWorkspace.Final.SourceBlock832Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock864DataFull
import ProofWorkspace.Final.EtaBlock864Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock864XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (864+k) (sourceBlock864PiPairs.getD k (0,0))
    (sourceEtaBatch864Lower k, sourceEtaBatch864Upper k)
    (sourceBlock864TwoPairs.getD k (0,0))

theorem sourceBlock864Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock864XiPair k).1:ℝ) ≤ (xi (xiGridArgument (864+k):ℂ)).re ∧
      (xi (xiGridArgument (864+k):ℂ)).re ≤ ((sourceBlock864XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (864+k) _ _ _
    (sourceBlock864PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch864_actual_enclosure k hk)
    (sourceBlock864TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock864Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock864XiPair k).1 := by
  decide +kernel

theorem sourceBlock864Reciprocal_check : ∀ k : Fin 32,
    sourceBlock864Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock864XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock864XiPair k)).2 ≤
      sourceBlock864Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block864_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((864+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (864+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock864Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (864+k) (sourceBlock864XiPair k) _
    (sourceBlock864Xi_enclosure k hk) (sourceBlock864Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock864Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first896_bound (k : ℕ) (hk : k < 896) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 864
  · exact sourceRoundedMidpoint_first864_bound k h
  · have hsum : 864+(k-864) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block864_bound (k-864) (by omega)

end ReciprocalXi
