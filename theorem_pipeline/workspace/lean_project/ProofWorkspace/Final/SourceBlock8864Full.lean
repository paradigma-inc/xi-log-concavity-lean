import ProofWorkspace.Final.SourceBlock8832Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8864DataFull
import ProofWorkspace.Final.EtaBlock8864Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8864XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8864+k) (sourceBlock8864PiPairs.getD k (0,0))
    (sourceEtaBatch8864Lower k, sourceEtaBatch8864Upper k)
    (sourceBlock8864TwoPairs.getD k (0,0))

theorem sourceBlock8864Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8864XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8864+k):ℂ)).re ∧
      (xi (xiGridArgument (8864+k):ℂ)).re ≤ ((sourceBlock8864XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8864+k) _ _ _
    (sourceBlock8864PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8864_actual_enclosure k hk)
    (sourceBlock8864TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8864Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8864XiPair k).1 := by
  decide +kernel

theorem sourceBlock8864Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8864Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8864XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8864XiPair k)).2 ≤
      sourceBlock8864Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8864_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8864+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8864+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8864Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8864+k) (sourceBlock8864XiPair k) _
    (sourceBlock8864Xi_enclosure k hk) (sourceBlock8864Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8864Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8896_bound (k : ℕ) (hk : k < 8896) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8864
  · exact sourceRoundedMidpoint_first8864_bound k h
  · have hsum : 8864+(k-8864) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8864_bound (k-8864) (by omega)

end ReciprocalXi
