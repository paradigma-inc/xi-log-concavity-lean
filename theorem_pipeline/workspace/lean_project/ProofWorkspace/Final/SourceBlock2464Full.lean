import ProofWorkspace.Final.SourceBlock2432Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2464DataFull
import ProofWorkspace.Final.EtaBlock2464Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2464XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2464+k) (sourceBlock2464PiPairs.getD k (0,0))
    (sourceEtaBatch2464Lower k, sourceEtaBatch2464Upper k)
    (sourceBlock2464TwoPairs.getD k (0,0))

theorem sourceBlock2464Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2464XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2464+k):ℂ)).re ∧
      (xi (xiGridArgument (2464+k):ℂ)).re ≤ ((sourceBlock2464XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2464+k) _ _ _
    (sourceBlock2464PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2464_actual_enclosure k hk)
    (sourceBlock2464TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2464Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2464XiPair k).1 := by
  decide +kernel

theorem sourceBlock2464Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2464Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2464XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2464XiPair k)).2 ≤
      sourceBlock2464Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2464_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2464+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2464+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2464Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2464+k) (sourceBlock2464XiPair k) _
    (sourceBlock2464Xi_enclosure k hk) (sourceBlock2464Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2464Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2496_bound (k : ℕ) (hk : k < 2496) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2464
  · exact sourceRoundedMidpoint_first2464_bound k h
  · have hsum : 2464+(k-2464) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2464_bound (k-2464) (by omega)

end ReciprocalXi
