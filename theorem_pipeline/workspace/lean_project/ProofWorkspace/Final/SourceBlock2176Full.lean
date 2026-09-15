import ProofWorkspace.Final.SourceBlock2144Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2176DataFull
import ProofWorkspace.Final.EtaBlock2176Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2176XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2176+k) (sourceBlock2176PiPairs.getD k (0,0))
    (sourceEtaBatch2176Lower k, sourceEtaBatch2176Upper k)
    (sourceBlock2176TwoPairs.getD k (0,0))

theorem sourceBlock2176Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2176XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2176+k):ℂ)).re ∧
      (xi (xiGridArgument (2176+k):ℂ)).re ≤ ((sourceBlock2176XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2176+k) _ _ _
    (sourceBlock2176PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2176_actual_enclosure k hk)
    (sourceBlock2176TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2176Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2176XiPair k).1 := by
  decide +kernel

theorem sourceBlock2176Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2176Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2176XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2176XiPair k)).2 ≤
      sourceBlock2176Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2176_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2176+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2176+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2176Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2176+k) (sourceBlock2176XiPair k) _
    (sourceBlock2176Xi_enclosure k hk) (sourceBlock2176Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2176Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2208_bound (k : ℕ) (hk : k < 2208) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2176
  · exact sourceRoundedMidpoint_first2176_bound k h
  · have hsum : 2176+(k-2176) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2176_bound (k-2176) (by omega)

end ReciprocalXi
