import ProofWorkspace.Final.SourceBlock4000Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4032DataFull
import ProofWorkspace.Final.EtaBlock4032Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4032XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4032+k) (sourceBlock4032PiPairs.getD k (0,0))
    (sourceEtaBatch4032Lower k, sourceEtaBatch4032Upper k)
    (sourceBlock4032TwoPairs.getD k (0,0))

theorem sourceBlock4032Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4032XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4032+k):ℂ)).re ∧
      (xi (xiGridArgument (4032+k):ℂ)).re ≤ ((sourceBlock4032XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4032+k) _ _ _
    (sourceBlock4032PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4032_actual_enclosure k hk)
    (sourceBlock4032TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4032Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4032XiPair k).1 := by
  decide +kernel

theorem sourceBlock4032Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4032Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4032XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4032XiPair k)).2 ≤
      sourceBlock4032Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4032_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4032+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4032+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4032Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4032+k) (sourceBlock4032XiPair k) _
    (sourceBlock4032Xi_enclosure k hk) (sourceBlock4032Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4032Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4064_bound (k : ℕ) (hk : k < 4064) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4032
  · exact sourceRoundedMidpoint_first4032_bound k h
  · have hsum : 4032+(k-4032) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4032_bound (k-4032) (by omega)

end ReciprocalXi
