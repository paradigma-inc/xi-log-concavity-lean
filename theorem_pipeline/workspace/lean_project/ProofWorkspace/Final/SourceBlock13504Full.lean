import ProofWorkspace.Final.SourceBlock13472Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13504DataFull
import ProofWorkspace.Final.EtaBlock13504Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13504XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13504+k) (sourceBlock13504PiPairs.getD k (0,0))
    (sourceEtaBatch13504Lower k, sourceEtaBatch13504Upper k)
    (sourceBlock13504TwoPairs.getD k (0,0))

theorem sourceBlock13504Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13504XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13504+k):ℂ)).re ∧
      (xi (xiGridArgument (13504+k):ℂ)).re ≤ ((sourceBlock13504XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13504+k) _ _ _
    (sourceBlock13504PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13504_actual_enclosure k hk)
    (sourceBlock13504TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13504Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13504XiPair k).1 := by
  decide +kernel

theorem sourceBlock13504Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13504Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13504XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13504XiPair k)).2 ≤
      sourceBlock13504Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13504_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13504+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13504+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13504Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13504+k) (sourceBlock13504XiPair k) _
    (sourceBlock13504Xi_enclosure k hk) (sourceBlock13504Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13504Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13536_bound (k : ℕ) (hk : k < 13536) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13504
  · exact sourceRoundedMidpoint_first13504_bound k h
  · have hsum : 13504+(k-13504) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13504_bound (k-13504) (by omega)

end ReciprocalXi
