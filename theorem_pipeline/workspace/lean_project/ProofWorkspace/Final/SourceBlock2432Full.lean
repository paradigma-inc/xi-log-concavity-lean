import ProofWorkspace.Final.SourceBlock2400Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2432DataFull
import ProofWorkspace.Final.EtaBlock2432Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2432XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2432+k) (sourceBlock2432PiPairs.getD k (0,0))
    (sourceEtaBatch2432Lower k, sourceEtaBatch2432Upper k)
    (sourceBlock2432TwoPairs.getD k (0,0))

theorem sourceBlock2432Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2432XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2432+k):ℂ)).re ∧
      (xi (xiGridArgument (2432+k):ℂ)).re ≤ ((sourceBlock2432XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2432+k) _ _ _
    (sourceBlock2432PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2432_actual_enclosure k hk)
    (sourceBlock2432TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2432Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2432XiPair k).1 := by
  decide +kernel

theorem sourceBlock2432Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2432Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2432XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2432XiPair k)).2 ≤
      sourceBlock2432Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2432_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2432+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2432+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2432Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2432+k) (sourceBlock2432XiPair k) _
    (sourceBlock2432Xi_enclosure k hk) (sourceBlock2432Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2432Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2464_bound (k : ℕ) (hk : k < 2464) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2432
  · exact sourceRoundedMidpoint_first2432_bound k h
  · have hsum : 2432+(k-2432) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2432_bound (k-2432) (by omega)

end ReciprocalXi
