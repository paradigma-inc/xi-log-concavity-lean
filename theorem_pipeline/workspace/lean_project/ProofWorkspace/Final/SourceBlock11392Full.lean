import ProofWorkspace.Final.SourceBlock11360Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11392DataFull
import ProofWorkspace.Final.EtaBlock11392Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11392XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11392+k) (sourceBlock11392PiPairs.getD k (0,0))
    (sourceEtaBatch11392Lower k, sourceEtaBatch11392Upper k)
    (sourceBlock11392TwoPairs.getD k (0,0))

theorem sourceBlock11392Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11392XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11392+k):ℂ)).re ∧
      (xi (xiGridArgument (11392+k):ℂ)).re ≤ ((sourceBlock11392XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11392+k) _ _ _
    (sourceBlock11392PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11392_actual_enclosure k hk)
    (sourceBlock11392TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11392Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11392XiPair k).1 := by
  decide +kernel

theorem sourceBlock11392Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11392Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11392XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11392XiPair k)).2 ≤
      sourceBlock11392Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11392_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11392+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11392+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11392Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11392+k) (sourceBlock11392XiPair k) _
    (sourceBlock11392Xi_enclosure k hk) (sourceBlock11392Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11392Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11424_bound (k : ℕ) (hk : k < 11424) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11392
  · exact sourceRoundedMidpoint_first11392_bound k h
  · have hsum : 11392+(k-11392) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11392_bound (k-11392) (by omega)

end ReciprocalXi
