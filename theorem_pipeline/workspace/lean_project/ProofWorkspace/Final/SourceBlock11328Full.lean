import ProofWorkspace.Final.SourceBlock11296Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11328DataFull
import ProofWorkspace.Final.EtaBlock11328Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11328XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11328+k) (sourceBlock11328PiPairs.getD k (0,0))
    (sourceEtaBatch11328Lower k, sourceEtaBatch11328Upper k)
    (sourceBlock11328TwoPairs.getD k (0,0))

theorem sourceBlock11328Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11328XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11328+k):ℂ)).re ∧
      (xi (xiGridArgument (11328+k):ℂ)).re ≤ ((sourceBlock11328XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11328+k) _ _ _
    (sourceBlock11328PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11328_actual_enclosure k hk)
    (sourceBlock11328TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11328Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11328XiPair k).1 := by
  decide +kernel

theorem sourceBlock11328Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11328Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11328XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11328XiPair k)).2 ≤
      sourceBlock11328Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11328_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11328+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11328+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11328Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11328+k) (sourceBlock11328XiPair k) _
    (sourceBlock11328Xi_enclosure k hk) (sourceBlock11328Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11328Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11360_bound (k : ℕ) (hk : k < 11360) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11328
  · exact sourceRoundedMidpoint_first11328_bound k h
  · have hsum : 11328+(k-11328) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11328_bound (k-11328) (by omega)

end ReciprocalXi
