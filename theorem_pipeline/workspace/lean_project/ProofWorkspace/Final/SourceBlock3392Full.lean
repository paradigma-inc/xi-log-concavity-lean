import ProofWorkspace.Final.SourceBlock3360Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3392DataFull
import ProofWorkspace.Final.EtaBlock3392Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3392XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3392+k) (sourceBlock3392PiPairs.getD k (0,0))
    (sourceEtaBatch3392Lower k, sourceEtaBatch3392Upper k)
    (sourceBlock3392TwoPairs.getD k (0,0))

theorem sourceBlock3392Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3392XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3392+k):ℂ)).re ∧
      (xi (xiGridArgument (3392+k):ℂ)).re ≤ ((sourceBlock3392XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3392+k) _ _ _
    (sourceBlock3392PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3392_actual_enclosure k hk)
    (sourceBlock3392TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3392Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3392XiPair k).1 := by
  decide +kernel

theorem sourceBlock3392Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3392Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3392XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3392XiPair k)).2 ≤
      sourceBlock3392Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3392_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3392+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3392+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3392Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3392+k) (sourceBlock3392XiPair k) _
    (sourceBlock3392Xi_enclosure k hk) (sourceBlock3392Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3392Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3424_bound (k : ℕ) (hk : k < 3424) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3392
  · exact sourceRoundedMidpoint_first3392_bound k h
  · have hsum : 3392+(k-3392) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3392_bound (k-3392) (by omega)

end ReciprocalXi
