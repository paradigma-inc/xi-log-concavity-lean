import ProofWorkspace.Final.SourceBlock12384Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12416DataFull
import ProofWorkspace.Final.EtaBlock12416Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12416XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12416+k) (sourceBlock12416PiPairs.getD k (0,0))
    (sourceEtaBatch12416Lower k, sourceEtaBatch12416Upper k)
    (sourceBlock12416TwoPairs.getD k (0,0))

theorem sourceBlock12416Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12416XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12416+k):ℂ)).re ∧
      (xi (xiGridArgument (12416+k):ℂ)).re ≤ ((sourceBlock12416XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12416+k) _ _ _
    (sourceBlock12416PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12416_actual_enclosure k hk)
    (sourceBlock12416TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12416Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12416XiPair k).1 := by
  decide +kernel

theorem sourceBlock12416Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12416Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12416XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12416XiPair k)).2 ≤
      sourceBlock12416Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12416_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12416+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12416+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12416Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12416+k) (sourceBlock12416XiPair k) _
    (sourceBlock12416Xi_enclosure k hk) (sourceBlock12416Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12416Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12448_bound (k : ℕ) (hk : k < 12448) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12416
  · exact sourceRoundedMidpoint_first12416_bound k h
  · have hsum : 12416+(k-12416) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12416_bound (k-12416) (by omega)

end ReciprocalXi
