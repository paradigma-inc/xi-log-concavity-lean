import ProofWorkspace.Final.SourceBlock8160Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8192DataFull
import ProofWorkspace.Final.EtaBlock8192Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8192XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8192+k) (sourceBlock8192PiPairs.getD k (0,0))
    (sourceEtaBatch8192Lower k, sourceEtaBatch8192Upper k)
    (sourceBlock8192TwoPairs.getD k (0,0))

theorem sourceBlock8192Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8192XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8192+k):ℂ)).re ∧
      (xi (xiGridArgument (8192+k):ℂ)).re ≤ ((sourceBlock8192XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8192+k) _ _ _
    (sourceBlock8192PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8192_actual_enclosure k hk)
    (sourceBlock8192TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8192Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8192XiPair k).1 := by
  decide +kernel

theorem sourceBlock8192Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8192Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8192XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8192XiPair k)).2 ≤
      sourceBlock8192Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8192_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8192+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8192+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8192Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8192+k) (sourceBlock8192XiPair k) _
    (sourceBlock8192Xi_enclosure k hk) (sourceBlock8192Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8192Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8224_bound (k : ℕ) (hk : k < 8224) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8192
  · exact sourceRoundedMidpoint_first8192_bound k h
  · have hsum : 8192+(k-8192) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8192_bound (k-8192) (by omega)

end ReciprocalXi
