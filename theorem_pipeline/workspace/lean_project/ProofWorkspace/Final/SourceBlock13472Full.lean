import ProofWorkspace.Final.SourceBlock13440Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13472DataFull
import ProofWorkspace.Final.EtaBlock13472Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13472XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13472+k) (sourceBlock13472PiPairs.getD k (0,0))
    (sourceEtaBatch13472Lower k, sourceEtaBatch13472Upper k)
    (sourceBlock13472TwoPairs.getD k (0,0))

theorem sourceBlock13472Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13472XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13472+k):ℂ)).re ∧
      (xi (xiGridArgument (13472+k):ℂ)).re ≤ ((sourceBlock13472XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13472+k) _ _ _
    (sourceBlock13472PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13472_actual_enclosure k hk)
    (sourceBlock13472TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13472Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13472XiPair k).1 := by
  decide +kernel

theorem sourceBlock13472Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13472Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13472XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13472XiPair k)).2 ≤
      sourceBlock13472Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13472_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13472+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13472+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13472Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13472+k) (sourceBlock13472XiPair k) _
    (sourceBlock13472Xi_enclosure k hk) (sourceBlock13472Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13472Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13504_bound (k : ℕ) (hk : k < 13504) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13472
  · exact sourceRoundedMidpoint_first13472_bound k h
  · have hsum : 13472+(k-13472) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13472_bound (k-13472) (by omega)

end ReciprocalXi
