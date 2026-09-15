import ProofWorkspace.Final.SourceBlock7360Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7392DataFull
import ProofWorkspace.Final.EtaBlock7392Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7392XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7392+k) (sourceBlock7392PiPairs.getD k (0,0))
    (sourceEtaBatch7392Lower k, sourceEtaBatch7392Upper k)
    (sourceBlock7392TwoPairs.getD k (0,0))

theorem sourceBlock7392Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7392XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7392+k):ℂ)).re ∧
      (xi (xiGridArgument (7392+k):ℂ)).re ≤ ((sourceBlock7392XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7392+k) _ _ _
    (sourceBlock7392PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7392_actual_enclosure k hk)
    (sourceBlock7392TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7392Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7392XiPair k).1 := by
  decide +kernel

theorem sourceBlock7392Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7392Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7392XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7392XiPair k)).2 ≤
      sourceBlock7392Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7392_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7392+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7392+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7392Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7392+k) (sourceBlock7392XiPair k) _
    (sourceBlock7392Xi_enclosure k hk) (sourceBlock7392Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7392Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7424_bound (k : ℕ) (hk : k < 7424) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7392
  · exact sourceRoundedMidpoint_first7392_bound k h
  · have hsum : 7392+(k-7392) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7392_bound (k-7392) (by omega)

end ReciprocalXi
