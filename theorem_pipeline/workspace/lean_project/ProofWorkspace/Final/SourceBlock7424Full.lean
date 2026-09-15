import ProofWorkspace.Final.SourceBlock7392Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7424DataFull
import ProofWorkspace.Final.EtaBlock7424Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7424XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7424+k) (sourceBlock7424PiPairs.getD k (0,0))
    (sourceEtaBatch7424Lower k, sourceEtaBatch7424Upper k)
    (sourceBlock7424TwoPairs.getD k (0,0))

theorem sourceBlock7424Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7424XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7424+k):ℂ)).re ∧
      (xi (xiGridArgument (7424+k):ℂ)).re ≤ ((sourceBlock7424XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7424+k) _ _ _
    (sourceBlock7424PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7424_actual_enclosure k hk)
    (sourceBlock7424TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7424Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7424XiPair k).1 := by
  decide +kernel

theorem sourceBlock7424Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7424Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7424XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7424XiPair k)).2 ≤
      sourceBlock7424Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7424_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7424+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7424+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7424Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7424+k) (sourceBlock7424XiPair k) _
    (sourceBlock7424Xi_enclosure k hk) (sourceBlock7424Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7424Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7456_bound (k : ℕ) (hk : k < 7456) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7424
  · exact sourceRoundedMidpoint_first7424_bound k h
  · have hsum : 7424+(k-7424) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7424_bound (k-7424) (by omega)

end ReciprocalXi
