import ProofWorkspace.Final.SourceBlock3392Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3424DataFull
import ProofWorkspace.Final.EtaBlock3424Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3424XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3424+k) (sourceBlock3424PiPairs.getD k (0,0))
    (sourceEtaBatch3424Lower k, sourceEtaBatch3424Upper k)
    (sourceBlock3424TwoPairs.getD k (0,0))

theorem sourceBlock3424Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3424XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3424+k):ℂ)).re ∧
      (xi (xiGridArgument (3424+k):ℂ)).re ≤ ((sourceBlock3424XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3424+k) _ _ _
    (sourceBlock3424PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3424_actual_enclosure k hk)
    (sourceBlock3424TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3424Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3424XiPair k).1 := by
  decide +kernel

theorem sourceBlock3424Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3424Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3424XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3424XiPair k)).2 ≤
      sourceBlock3424Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3424_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3424+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3424+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3424Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3424+k) (sourceBlock3424XiPair k) _
    (sourceBlock3424Xi_enclosure k hk) (sourceBlock3424Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3424Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3456_bound (k : ℕ) (hk : k < 3456) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3424
  · exact sourceRoundedMidpoint_first3424_bound k h
  · have hsum : 3424+(k-3424) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3424_bound (k-3424) (by omega)

end ReciprocalXi
