import ProofWorkspace.Final.SourceBlock5248Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5280DataFull
import ProofWorkspace.Final.EtaBlock5280Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5280XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5280+k) (sourceBlock5280PiPairs.getD k (0,0))
    (sourceEtaBatch5280Lower k, sourceEtaBatch5280Upper k)
    (sourceBlock5280TwoPairs.getD k (0,0))

theorem sourceBlock5280Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5280XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5280+k):ℂ)).re ∧
      (xi (xiGridArgument (5280+k):ℂ)).re ≤ ((sourceBlock5280XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5280+k) _ _ _
    (sourceBlock5280PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5280_actual_enclosure k hk)
    (sourceBlock5280TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5280Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5280XiPair k).1 := by
  decide +kernel

theorem sourceBlock5280Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5280Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5280XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5280XiPair k)).2 ≤
      sourceBlock5280Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5280_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5280+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5280+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5280Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5280+k) (sourceBlock5280XiPair k) _
    (sourceBlock5280Xi_enclosure k hk) (sourceBlock5280Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5280Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5312_bound (k : ℕ) (hk : k < 5312) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5280
  · exact sourceRoundedMidpoint_first5280_bound k h
  · have hsum : 5280+(k-5280) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5280_bound (k-5280) (by omega)

end ReciprocalXi
