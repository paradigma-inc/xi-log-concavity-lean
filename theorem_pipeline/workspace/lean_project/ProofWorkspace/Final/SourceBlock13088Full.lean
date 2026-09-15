import ProofWorkspace.Final.SourceBlock13056Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13088DataFull
import ProofWorkspace.Final.EtaBlock13088Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13088XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13088+k) (sourceBlock13088PiPairs.getD k (0,0))
    (sourceEtaBatch13088Lower k, sourceEtaBatch13088Upper k)
    (sourceBlock13088TwoPairs.getD k (0,0))

theorem sourceBlock13088Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13088XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13088+k):ℂ)).re ∧
      (xi (xiGridArgument (13088+k):ℂ)).re ≤ ((sourceBlock13088XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13088+k) _ _ _
    (sourceBlock13088PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13088_actual_enclosure k hk)
    (sourceBlock13088TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13088Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13088XiPair k).1 := by
  decide +kernel

theorem sourceBlock13088Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13088Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13088XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13088XiPair k)).2 ≤
      sourceBlock13088Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13088_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13088+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13088+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13088Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13088+k) (sourceBlock13088XiPair k) _
    (sourceBlock13088Xi_enclosure k hk) (sourceBlock13088Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13088Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13120_bound (k : ℕ) (hk : k < 13120) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13088
  · exact sourceRoundedMidpoint_first13088_bound k h
  · have hsum : 13088+(k-13088) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13088_bound (k-13088) (by omega)

end ReciprocalXi
