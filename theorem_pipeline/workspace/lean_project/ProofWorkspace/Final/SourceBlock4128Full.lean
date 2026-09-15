import ProofWorkspace.Final.SourceBlock4096Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4128DataFull
import ProofWorkspace.Final.EtaBlock4128Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4128XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4128+k) (sourceBlock4128PiPairs.getD k (0,0))
    (sourceEtaBatch4128Lower k, sourceEtaBatch4128Upper k)
    (sourceBlock4128TwoPairs.getD k (0,0))

theorem sourceBlock4128Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4128XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4128+k):ℂ)).re ∧
      (xi (xiGridArgument (4128+k):ℂ)).re ≤ ((sourceBlock4128XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4128+k) _ _ _
    (sourceBlock4128PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4128_actual_enclosure k hk)
    (sourceBlock4128TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4128Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4128XiPair k).1 := by
  decide +kernel

theorem sourceBlock4128Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4128Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4128XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4128XiPair k)).2 ≤
      sourceBlock4128Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4128_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4128+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4128+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4128Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4128+k) (sourceBlock4128XiPair k) _
    (sourceBlock4128Xi_enclosure k hk) (sourceBlock4128Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4128Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4160_bound (k : ℕ) (hk : k < 4160) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4128
  · exact sourceRoundedMidpoint_first4128_bound k h
  · have hsum : 4128+(k-4128) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4128_bound (k-4128) (by omega)

end ReciprocalXi
