import ProofWorkspace.Final.SourceBlock6784Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6816DataFull
import ProofWorkspace.Final.EtaBlock6816Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6816XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6816+k) (sourceBlock6816PiPairs.getD k (0,0))
    (sourceEtaBatch6816Lower k, sourceEtaBatch6816Upper k)
    (sourceBlock6816TwoPairs.getD k (0,0))

theorem sourceBlock6816Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6816XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6816+k):ℂ)).re ∧
      (xi (xiGridArgument (6816+k):ℂ)).re ≤ ((sourceBlock6816XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6816+k) _ _ _
    (sourceBlock6816PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6816_actual_enclosure k hk)
    (sourceBlock6816TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6816Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6816XiPair k).1 := by
  decide +kernel

theorem sourceBlock6816Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6816Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6816XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6816XiPair k)).2 ≤
      sourceBlock6816Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6816_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6816+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6816+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6816Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6816+k) (sourceBlock6816XiPair k) _
    (sourceBlock6816Xi_enclosure k hk) (sourceBlock6816Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6816Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6848_bound (k : ℕ) (hk : k < 6848) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6816
  · exact sourceRoundedMidpoint_first6816_bound k h
  · have hsum : 6816+(k-6816) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6816_bound (k-6816) (by omega)

end ReciprocalXi
