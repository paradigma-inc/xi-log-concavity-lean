import ProofWorkspace.Final.SourceBlock12032Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12064DataFull
import ProofWorkspace.Final.EtaBlock12064Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12064XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12064+k) (sourceBlock12064PiPairs.getD k (0,0))
    (sourceEtaBatch12064Lower k, sourceEtaBatch12064Upper k)
    (sourceBlock12064TwoPairs.getD k (0,0))

theorem sourceBlock12064Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12064XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12064+k):ℂ)).re ∧
      (xi (xiGridArgument (12064+k):ℂ)).re ≤ ((sourceBlock12064XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12064+k) _ _ _
    (sourceBlock12064PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12064_actual_enclosure k hk)
    (sourceBlock12064TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12064Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12064XiPair k).1 := by
  decide +kernel

theorem sourceBlock12064Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12064Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12064XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12064XiPair k)).2 ≤
      sourceBlock12064Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12064_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12064+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12064+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12064Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12064+k) (sourceBlock12064XiPair k) _
    (sourceBlock12064Xi_enclosure k hk) (sourceBlock12064Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12064Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12096_bound (k : ℕ) (hk : k < 12096) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12064
  · exact sourceRoundedMidpoint_first12064_bound k h
  · have hsum : 12064+(k-12064) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12064_bound (k-12064) (by omega)

end ReciprocalXi
