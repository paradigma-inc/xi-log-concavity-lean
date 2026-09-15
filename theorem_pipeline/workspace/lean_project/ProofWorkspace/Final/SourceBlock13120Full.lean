import ProofWorkspace.Final.SourceBlock13088Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13120DataFull
import ProofWorkspace.Final.EtaBlock13120Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13120XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13120+k) (sourceBlock13120PiPairs.getD k (0,0))
    (sourceEtaBatch13120Lower k, sourceEtaBatch13120Upper k)
    (sourceBlock13120TwoPairs.getD k (0,0))

theorem sourceBlock13120Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13120XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13120+k):ℂ)).re ∧
      (xi (xiGridArgument (13120+k):ℂ)).re ≤ ((sourceBlock13120XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13120+k) _ _ _
    (sourceBlock13120PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13120_actual_enclosure k hk)
    (sourceBlock13120TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13120Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13120XiPair k).1 := by
  decide +kernel

theorem sourceBlock13120Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13120Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13120XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13120XiPair k)).2 ≤
      sourceBlock13120Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13120_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13120+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13120+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13120Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13120+k) (sourceBlock13120XiPair k) _
    (sourceBlock13120Xi_enclosure k hk) (sourceBlock13120Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13120Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13152_bound (k : ℕ) (hk : k < 13152) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13120
  · exact sourceRoundedMidpoint_first13120_bound k h
  · have hsum : 13120+(k-13120) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13120_bound (k-13120) (by omega)

end ReciprocalXi
