import ProofWorkspace.Final.SourceBlock6400Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6432DataFull
import ProofWorkspace.Final.EtaBlock6432Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6432XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6432+k) (sourceBlock6432PiPairs.getD k (0,0))
    (sourceEtaBatch6432Lower k, sourceEtaBatch6432Upper k)
    (sourceBlock6432TwoPairs.getD k (0,0))

theorem sourceBlock6432Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6432XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6432+k):ℂ)).re ∧
      (xi (xiGridArgument (6432+k):ℂ)).re ≤ ((sourceBlock6432XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6432+k) _ _ _
    (sourceBlock6432PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6432_actual_enclosure k hk)
    (sourceBlock6432TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6432Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6432XiPair k).1 := by
  decide +kernel

theorem sourceBlock6432Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6432Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6432XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6432XiPair k)).2 ≤
      sourceBlock6432Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6432_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6432+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6432+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6432Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6432+k) (sourceBlock6432XiPair k) _
    (sourceBlock6432Xi_enclosure k hk) (sourceBlock6432Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6432Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6464_bound (k : ℕ) (hk : k < 6464) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6432
  · exact sourceRoundedMidpoint_first6432_bound k h
  · have hsum : 6432+(k-6432) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6432_bound (k-6432) (by omega)

end ReciprocalXi
