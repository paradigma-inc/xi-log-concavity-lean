import ProofWorkspace.Final.SourceBlock960Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock992DataFull
import ProofWorkspace.Final.EtaBlock992Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock992XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (992+k) (sourceBlock992PiPairs.getD k (0,0))
    (sourceEtaBatch992Lower k, sourceEtaBatch992Upper k)
    (sourceBlock992TwoPairs.getD k (0,0))

theorem sourceBlock992Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock992XiPair k).1:ℝ) ≤ (xi (xiGridArgument (992+k):ℂ)).re ∧
      (xi (xiGridArgument (992+k):ℂ)).re ≤ ((sourceBlock992XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (992+k) _ _ _
    (sourceBlock992PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch992_actual_enclosure k hk)
    (sourceBlock992TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock992Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock992XiPair k).1 := by
  decide +kernel

theorem sourceBlock992Reciprocal_check : ∀ k : Fin 32,
    sourceBlock992Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock992XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock992XiPair k)).2 ≤
      sourceBlock992Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block992_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((992+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (992+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock992Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (992+k) (sourceBlock992XiPair k) _
    (sourceBlock992Xi_enclosure k hk) (sourceBlock992Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock992Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1024_bound (k : ℕ) (hk : k < 1024) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 992
  · exact sourceRoundedMidpoint_first992_bound k h
  · have hsum : 992+(k-992) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block992_bound (k-992) (by omega)

end ReciprocalXi
