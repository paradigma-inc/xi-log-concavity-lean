import ProofWorkspace.Final.SourceBlock13568Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13600DataFull
import ProofWorkspace.Final.EtaBlock13600Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13600XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13600+k) (sourceBlock13600PiPairs.getD k (0,0))
    (sourceEtaBatch13600Lower k, sourceEtaBatch13600Upper k)
    (sourceBlock13600TwoPairs.getD k (0,0))

theorem sourceBlock13600Xi_enclosure (k : ℕ) (hk : k < 1) :
    ((sourceBlock13600XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13600+k):ℂ)).re ∧
      (xi (xiGridArgument (13600+k):ℂ)).re ≤ ((sourceBlock13600XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13600+k) _ _ _
    (sourceBlock13600PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13600_actual_enclosure k hk)
    (sourceBlock13600TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13600Xi_positive_checked : ∀ k : Fin 1,
    0 < (sourceBlock13600XiPair k).1 := by
  decide +kernel

theorem sourceBlock13600Reciprocal_check : ∀ k : Fin 1,
    sourceBlock13600Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13600XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13600XiPair k)).2 ≤
      sourceBlock13600Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13600_bound (k : ℕ) (hk : k < 1) :
    |(reciprocalTransform (((13600+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13600+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13600Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13600+k) (sourceBlock13600XiPair k) _
    (sourceBlock13600Xi_enclosure k hk) (sourceBlock13600Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13600Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13601_bound (k : ℕ) (hk : k < 13601) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13600
  · exact sourceRoundedMidpoint_first13600_bound k h
  · have hsum : 13600+(k-13600) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13600_bound (k-13600) (by omega)

end ReciprocalXi
