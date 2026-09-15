import ProofWorkspace.Final.SourceBlock5920Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5952DataFull
import ProofWorkspace.Final.EtaBlock5952Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5952XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5952+k) (sourceBlock5952PiPairs.getD k (0,0))
    (sourceEtaBatch5952Lower k, sourceEtaBatch5952Upper k)
    (sourceBlock5952TwoPairs.getD k (0,0))

theorem sourceBlock5952Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5952XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5952+k):ℂ)).re ∧
      (xi (xiGridArgument (5952+k):ℂ)).re ≤ ((sourceBlock5952XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5952+k) _ _ _
    (sourceBlock5952PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5952_actual_enclosure k hk)
    (sourceBlock5952TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5952Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5952XiPair k).1 := by
  decide +kernel

theorem sourceBlock5952Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5952Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5952XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5952XiPair k)).2 ≤
      sourceBlock5952Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5952_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5952+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5952+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5952Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5952+k) (sourceBlock5952XiPair k) _
    (sourceBlock5952Xi_enclosure k hk) (sourceBlock5952Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5952Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5984_bound (k : ℕ) (hk : k < 5984) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5952
  · exact sourceRoundedMidpoint_first5952_bound k h
  · have hsum : 5952+(k-5952) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5952_bound (k-5952) (by omega)

end ReciprocalXi
