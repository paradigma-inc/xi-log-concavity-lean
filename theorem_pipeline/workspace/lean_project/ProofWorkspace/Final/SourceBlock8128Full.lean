import ProofWorkspace.Final.SourceBlock8096Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8128DataFull
import ProofWorkspace.Final.EtaBlock8128Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8128XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8128+k) (sourceBlock8128PiPairs.getD k (0,0))
    (sourceEtaBatch8128Lower k, sourceEtaBatch8128Upper k)
    (sourceBlock8128TwoPairs.getD k (0,0))

theorem sourceBlock8128Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8128XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8128+k):ℂ)).re ∧
      (xi (xiGridArgument (8128+k):ℂ)).re ≤ ((sourceBlock8128XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8128+k) _ _ _
    (sourceBlock8128PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8128_actual_enclosure k hk)
    (sourceBlock8128TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8128Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8128XiPair k).1 := by
  decide +kernel

theorem sourceBlock8128Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8128Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8128XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8128XiPair k)).2 ≤
      sourceBlock8128Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8128_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8128+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8128+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8128Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8128+k) (sourceBlock8128XiPair k) _
    (sourceBlock8128Xi_enclosure k hk) (sourceBlock8128Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8128Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8160_bound (k : ℕ) (hk : k < 8160) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8128
  · exact sourceRoundedMidpoint_first8128_bound k h
  · have hsum : 8128+(k-8128) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8128_bound (k-8128) (by omega)

end ReciprocalXi
