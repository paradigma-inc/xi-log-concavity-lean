import ProofWorkspace.Final.SourceBlock1408Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1440DataFull
import ProofWorkspace.Final.EtaBlock1440Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1440XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1440+k) (sourceBlock1440PiPairs.getD k (0,0))
    (sourceEtaBatch1440Lower k, sourceEtaBatch1440Upper k)
    (sourceBlock1440TwoPairs.getD k (0,0))

theorem sourceBlock1440Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1440XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1440+k):ℂ)).re ∧
      (xi (xiGridArgument (1440+k):ℂ)).re ≤ ((sourceBlock1440XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1440+k) _ _ _
    (sourceBlock1440PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1440_actual_enclosure k hk)
    (sourceBlock1440TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1440Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1440XiPair k).1 := by
  decide +kernel

theorem sourceBlock1440Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1440Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1440XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1440XiPair k)).2 ≤
      sourceBlock1440Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1440_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1440+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1440+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1440Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1440+k) (sourceBlock1440XiPair k) _
    (sourceBlock1440Xi_enclosure k hk) (sourceBlock1440Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1440Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1472_bound (k : ℕ) (hk : k < 1472) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1440
  · exact sourceRoundedMidpoint_first1440_bound k h
  · have hsum : 1440+(k-1440) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1440_bound (k-1440) (by omega)

end ReciprocalXi
