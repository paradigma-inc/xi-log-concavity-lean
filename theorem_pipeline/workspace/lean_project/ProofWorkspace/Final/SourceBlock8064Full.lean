import ProofWorkspace.Final.SourceBlock8032Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8064DataFull
import ProofWorkspace.Final.EtaBlock8064Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8064XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8064+k) (sourceBlock8064PiPairs.getD k (0,0))
    (sourceEtaBatch8064Lower k, sourceEtaBatch8064Upper k)
    (sourceBlock8064TwoPairs.getD k (0,0))

theorem sourceBlock8064Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8064XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8064+k):ℂ)).re ∧
      (xi (xiGridArgument (8064+k):ℂ)).re ≤ ((sourceBlock8064XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8064+k) _ _ _
    (sourceBlock8064PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8064_actual_enclosure k hk)
    (sourceBlock8064TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8064Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8064XiPair k).1 := by
  decide +kernel

theorem sourceBlock8064Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8064Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8064XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8064XiPair k)).2 ≤
      sourceBlock8064Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8064_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8064+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8064+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8064Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8064+k) (sourceBlock8064XiPair k) _
    (sourceBlock8064Xi_enclosure k hk) (sourceBlock8064Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8064Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8096_bound (k : ℕ) (hk : k < 8096) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8064
  · exact sourceRoundedMidpoint_first8064_bound k h
  · have hsum : 8064+(k-8064) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8064_bound (k-8064) (by omega)

end ReciprocalXi
