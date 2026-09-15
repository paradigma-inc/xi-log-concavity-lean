import ProofWorkspace.Final.SourceBlock10784Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10816DataFull
import ProofWorkspace.Final.EtaBlock10816Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10816XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10816+k) (sourceBlock10816PiPairs.getD k (0,0))
    (sourceEtaBatch10816Lower k, sourceEtaBatch10816Upper k)
    (sourceBlock10816TwoPairs.getD k (0,0))

theorem sourceBlock10816Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10816XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10816+k):ℂ)).re ∧
      (xi (xiGridArgument (10816+k):ℂ)).re ≤ ((sourceBlock10816XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10816+k) _ _ _
    (sourceBlock10816PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10816_actual_enclosure k hk)
    (sourceBlock10816TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10816Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10816XiPair k).1 := by
  decide +kernel

theorem sourceBlock10816Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10816Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10816XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10816XiPair k)).2 ≤
      sourceBlock10816Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10816_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10816+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10816+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10816Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10816+k) (sourceBlock10816XiPair k) _
    (sourceBlock10816Xi_enclosure k hk) (sourceBlock10816Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10816Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10848_bound (k : ℕ) (hk : k < 10848) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10816
  · exact sourceRoundedMidpoint_first10816_bound k h
  · have hsum : 10816+(k-10816) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10816_bound (k-10816) (by omega)

end ReciprocalXi
