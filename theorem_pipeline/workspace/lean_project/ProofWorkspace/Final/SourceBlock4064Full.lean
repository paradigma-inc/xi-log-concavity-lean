import ProofWorkspace.Final.SourceBlock4032Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4064DataFull
import ProofWorkspace.Final.EtaBlock4064Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4064XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4064+k) (sourceBlock4064PiPairs.getD k (0,0))
    (sourceEtaBatch4064Lower k, sourceEtaBatch4064Upper k)
    (sourceBlock4064TwoPairs.getD k (0,0))

theorem sourceBlock4064Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4064XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4064+k):ℂ)).re ∧
      (xi (xiGridArgument (4064+k):ℂ)).re ≤ ((sourceBlock4064XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4064+k) _ _ _
    (sourceBlock4064PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4064_actual_enclosure k hk)
    (sourceBlock4064TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4064Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4064XiPair k).1 := by
  decide +kernel

theorem sourceBlock4064Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4064Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4064XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4064XiPair k)).2 ≤
      sourceBlock4064Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4064_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4064+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4064+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4064Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4064+k) (sourceBlock4064XiPair k) _
    (sourceBlock4064Xi_enclosure k hk) (sourceBlock4064Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4064Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4096_bound (k : ℕ) (hk : k < 4096) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4064
  · exact sourceRoundedMidpoint_first4064_bound k h
  · have hsum : 4064+(k-4064) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4064_bound (k-4064) (by omega)

end ReciprocalXi
