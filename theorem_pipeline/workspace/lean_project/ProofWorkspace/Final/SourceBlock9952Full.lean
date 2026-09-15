import ProofWorkspace.Final.SourceBlock9920Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9952DataFull
import ProofWorkspace.Final.EtaBlock9952Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9952XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9952+k) (sourceBlock9952PiPairs.getD k (0,0))
    (sourceEtaBatch9952Lower k, sourceEtaBatch9952Upper k)
    (sourceBlock9952TwoPairs.getD k (0,0))

theorem sourceBlock9952Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9952XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9952+k):ℂ)).re ∧
      (xi (xiGridArgument (9952+k):ℂ)).re ≤ ((sourceBlock9952XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9952+k) _ _ _
    (sourceBlock9952PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9952_actual_enclosure k hk)
    (sourceBlock9952TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9952Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9952XiPair k).1 := by
  decide +kernel

theorem sourceBlock9952Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9952Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9952XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9952XiPair k)).2 ≤
      sourceBlock9952Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9952_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9952+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9952+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9952Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9952+k) (sourceBlock9952XiPair k) _
    (sourceBlock9952Xi_enclosure k hk) (sourceBlock9952Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9952Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9984_bound (k : ℕ) (hk : k < 9984) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9952
  · exact sourceRoundedMidpoint_first9952_bound k h
  · have hsum : 9952+(k-9952) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9952_bound (k-9952) (by omega)

end ReciprocalXi
