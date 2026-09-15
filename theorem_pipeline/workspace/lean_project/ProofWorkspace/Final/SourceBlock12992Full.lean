import ProofWorkspace.Final.SourceBlock12960Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12992DataFull
import ProofWorkspace.Final.EtaBlock12992Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12992XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12992+k) (sourceBlock12992PiPairs.getD k (0,0))
    (sourceEtaBatch12992Lower k, sourceEtaBatch12992Upper k)
    (sourceBlock12992TwoPairs.getD k (0,0))

theorem sourceBlock12992Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12992XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12992+k):ℂ)).re ∧
      (xi (xiGridArgument (12992+k):ℂ)).re ≤ ((sourceBlock12992XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12992+k) _ _ _
    (sourceBlock12992PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12992_actual_enclosure k hk)
    (sourceBlock12992TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12992Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12992XiPair k).1 := by
  decide +kernel

theorem sourceBlock12992Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12992Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12992XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12992XiPair k)).2 ≤
      sourceBlock12992Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12992_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12992+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12992+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12992Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12992+k) (sourceBlock12992XiPair k) _
    (sourceBlock12992Xi_enclosure k hk) (sourceBlock12992Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12992Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13024_bound (k : ℕ) (hk : k < 13024) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12992
  · exact sourceRoundedMidpoint_first12992_bound k h
  · have hsum : 12992+(k-12992) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12992_bound (k-12992) (by omega)

end ReciprocalXi
