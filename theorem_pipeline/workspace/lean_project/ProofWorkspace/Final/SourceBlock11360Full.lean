import ProofWorkspace.Final.SourceBlock11328Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11360DataFull
import ProofWorkspace.Final.EtaBlock11360Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11360XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11360+k) (sourceBlock11360PiPairs.getD k (0,0))
    (sourceEtaBatch11360Lower k, sourceEtaBatch11360Upper k)
    (sourceBlock11360TwoPairs.getD k (0,0))

theorem sourceBlock11360Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11360XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11360+k):ℂ)).re ∧
      (xi (xiGridArgument (11360+k):ℂ)).re ≤ ((sourceBlock11360XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11360+k) _ _ _
    (sourceBlock11360PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11360_actual_enclosure k hk)
    (sourceBlock11360TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11360Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11360XiPair k).1 := by
  decide +kernel

theorem sourceBlock11360Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11360Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11360XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11360XiPair k)).2 ≤
      sourceBlock11360Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11360_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11360+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11360+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11360Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11360+k) (sourceBlock11360XiPair k) _
    (sourceBlock11360Xi_enclosure k hk) (sourceBlock11360Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11360Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11392_bound (k : ℕ) (hk : k < 11392) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11360
  · exact sourceRoundedMidpoint_first11360_bound k h
  · have hsum : 11360+(k-11360) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11360_bound (k-11360) (by omega)

end ReciprocalXi
