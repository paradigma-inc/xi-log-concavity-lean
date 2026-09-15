import ProofWorkspace.Final.SourceBlock1920Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1952DataFull
import ProofWorkspace.Final.EtaBlock1952Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1952XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1952+k) (sourceBlock1952PiPairs.getD k (0,0))
    (sourceEtaBatch1952Lower k, sourceEtaBatch1952Upper k)
    (sourceBlock1952TwoPairs.getD k (0,0))

theorem sourceBlock1952Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1952XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1952+k):ℂ)).re ∧
      (xi (xiGridArgument (1952+k):ℂ)).re ≤ ((sourceBlock1952XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1952+k) _ _ _
    (sourceBlock1952PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1952_actual_enclosure k hk)
    (sourceBlock1952TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1952Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1952XiPair k).1 := by
  decide +kernel

theorem sourceBlock1952Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1952Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1952XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1952XiPair k)).2 ≤
      sourceBlock1952Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1952_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1952+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1952+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1952Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1952+k) (sourceBlock1952XiPair k) _
    (sourceBlock1952Xi_enclosure k hk) (sourceBlock1952Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1952Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1984_bound (k : ℕ) (hk : k < 1984) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1952
  · exact sourceRoundedMidpoint_first1952_bound k h
  · have hsum : 1952+(k-1952) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1952_bound (k-1952) (by omega)

end ReciprocalXi
