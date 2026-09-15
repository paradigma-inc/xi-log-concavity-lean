import ProofWorkspace.Final.SourceBlock12000Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12032DataFull
import ProofWorkspace.Final.EtaBlock12032Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12032XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12032+k) (sourceBlock12032PiPairs.getD k (0,0))
    (sourceEtaBatch12032Lower k, sourceEtaBatch12032Upper k)
    (sourceBlock12032TwoPairs.getD k (0,0))

theorem sourceBlock12032Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12032XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12032+k):ℂ)).re ∧
      (xi (xiGridArgument (12032+k):ℂ)).re ≤ ((sourceBlock12032XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12032+k) _ _ _
    (sourceBlock12032PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12032_actual_enclosure k hk)
    (sourceBlock12032TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12032Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12032XiPair k).1 := by
  decide +kernel

theorem sourceBlock12032Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12032Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12032XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12032XiPair k)).2 ≤
      sourceBlock12032Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12032_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12032+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12032+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12032Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12032+k) (sourceBlock12032XiPair k) _
    (sourceBlock12032Xi_enclosure k hk) (sourceBlock12032Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12032Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12064_bound (k : ℕ) (hk : k < 12064) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12032
  · exact sourceRoundedMidpoint_first12032_bound k h
  · have hsum : 12032+(k-12032) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12032_bound (k-12032) (by omega)

end ReciprocalXi
