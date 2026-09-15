import ProofWorkspace.Final.SourceBlock10400Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10432DataFull
import ProofWorkspace.Final.EtaBlock10432Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10432XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10432+k) (sourceBlock10432PiPairs.getD k (0,0))
    (sourceEtaBatch10432Lower k, sourceEtaBatch10432Upper k)
    (sourceBlock10432TwoPairs.getD k (0,0))

theorem sourceBlock10432Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10432XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10432+k):ℂ)).re ∧
      (xi (xiGridArgument (10432+k):ℂ)).re ≤ ((sourceBlock10432XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10432+k) _ _ _
    (sourceBlock10432PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10432_actual_enclosure k hk)
    (sourceBlock10432TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10432Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10432XiPair k).1 := by
  decide +kernel

theorem sourceBlock10432Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10432Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10432XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10432XiPair k)).2 ≤
      sourceBlock10432Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10432_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10432+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10432+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10432Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10432+k) (sourceBlock10432XiPair k) _
    (sourceBlock10432Xi_enclosure k hk) (sourceBlock10432Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10432Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10464_bound (k : ℕ) (hk : k < 10464) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10432
  · exact sourceRoundedMidpoint_first10432_bound k h
  · have hsum : 10432+(k-10432) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10432_bound (k-10432) (by omega)

end ReciprocalXi
