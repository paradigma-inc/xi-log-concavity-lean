import ProofWorkspace.Final.SourceBlock10208Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10240DataFull
import ProofWorkspace.Final.EtaBlock10240Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10240XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10240+k) (sourceBlock10240PiPairs.getD k (0,0))
    (sourceEtaBatch10240Lower k, sourceEtaBatch10240Upper k)
    (sourceBlock10240TwoPairs.getD k (0,0))

theorem sourceBlock10240Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10240XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10240+k):ℂ)).re ∧
      (xi (xiGridArgument (10240+k):ℂ)).re ≤ ((sourceBlock10240XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10240+k) _ _ _
    (sourceBlock10240PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10240_actual_enclosure k hk)
    (sourceBlock10240TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10240Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10240XiPair k).1 := by
  decide +kernel

theorem sourceBlock10240Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10240Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10240XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10240XiPair k)).2 ≤
      sourceBlock10240Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10240_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10240+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10240+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10240Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10240+k) (sourceBlock10240XiPair k) _
    (sourceBlock10240Xi_enclosure k hk) (sourceBlock10240Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10240Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10272_bound (k : ℕ) (hk : k < 10272) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10240
  · exact sourceRoundedMidpoint_first10240_bound k h
  · have hsum : 10240+(k-10240) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10240_bound (k-10240) (by omega)

end ReciprocalXi
