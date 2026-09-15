import ProofWorkspace.Final.SourceBlock7328Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7360DataFull
import ProofWorkspace.Final.EtaBlock7360Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7360XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7360+k) (sourceBlock7360PiPairs.getD k (0,0))
    (sourceEtaBatch7360Lower k, sourceEtaBatch7360Upper k)
    (sourceBlock7360TwoPairs.getD k (0,0))

theorem sourceBlock7360Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7360XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7360+k):ℂ)).re ∧
      (xi (xiGridArgument (7360+k):ℂ)).re ≤ ((sourceBlock7360XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7360+k) _ _ _
    (sourceBlock7360PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7360_actual_enclosure k hk)
    (sourceBlock7360TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7360Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7360XiPair k).1 := by
  decide +kernel

theorem sourceBlock7360Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7360Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7360XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7360XiPair k)).2 ≤
      sourceBlock7360Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7360_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7360+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7360+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7360Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7360+k) (sourceBlock7360XiPair k) _
    (sourceBlock7360Xi_enclosure k hk) (sourceBlock7360Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7360Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7392_bound (k : ℕ) (hk : k < 7392) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7360
  · exact sourceRoundedMidpoint_first7360_bound k h
  · have hsum : 7360+(k-7360) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7360_bound (k-7360) (by omega)

end ReciprocalXi
