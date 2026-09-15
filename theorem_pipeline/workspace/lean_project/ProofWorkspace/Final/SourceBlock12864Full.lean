import ProofWorkspace.Final.SourceBlock12832Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12864DataFull
import ProofWorkspace.Final.EtaBlock12864Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12864XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12864+k) (sourceBlock12864PiPairs.getD k (0,0))
    (sourceEtaBatch12864Lower k, sourceEtaBatch12864Upper k)
    (sourceBlock12864TwoPairs.getD k (0,0))

theorem sourceBlock12864Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12864XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12864+k):ℂ)).re ∧
      (xi (xiGridArgument (12864+k):ℂ)).re ≤ ((sourceBlock12864XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12864+k) _ _ _
    (sourceBlock12864PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12864_actual_enclosure k hk)
    (sourceBlock12864TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12864Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12864XiPair k).1 := by
  decide +kernel

theorem sourceBlock12864Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12864Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12864XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12864XiPair k)).2 ≤
      sourceBlock12864Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12864_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12864+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12864+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12864Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12864+k) (sourceBlock12864XiPair k) _
    (sourceBlock12864Xi_enclosure k hk) (sourceBlock12864Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12864Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12896_bound (k : ℕ) (hk : k < 12896) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12864
  · exact sourceRoundedMidpoint_first12864_bound k h
  · have hsum : 12864+(k-12864) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12864_bound (k-12864) (by omega)

end ReciprocalXi
