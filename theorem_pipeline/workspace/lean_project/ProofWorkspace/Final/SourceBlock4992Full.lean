import ProofWorkspace.Final.SourceBlock4960Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4992DataFull
import ProofWorkspace.Final.EtaBlock4992Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4992XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4992+k) (sourceBlock4992PiPairs.getD k (0,0))
    (sourceEtaBatch4992Lower k, sourceEtaBatch4992Upper k)
    (sourceBlock4992TwoPairs.getD k (0,0))

theorem sourceBlock4992Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4992XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4992+k):ℂ)).re ∧
      (xi (xiGridArgument (4992+k):ℂ)).re ≤ ((sourceBlock4992XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4992+k) _ _ _
    (sourceBlock4992PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4992_actual_enclosure k hk)
    (sourceBlock4992TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4992Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4992XiPair k).1 := by
  decide +kernel

theorem sourceBlock4992Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4992Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4992XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4992XiPair k)).2 ≤
      sourceBlock4992Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4992_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4992+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4992+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4992Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4992+k) (sourceBlock4992XiPair k) _
    (sourceBlock4992Xi_enclosure k hk) (sourceBlock4992Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4992Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5024_bound (k : ℕ) (hk : k < 5024) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4992
  · exact sourceRoundedMidpoint_first4992_bound k h
  · have hsum : 4992+(k-4992) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4992_bound (k-4992) (by omega)

end ReciprocalXi
