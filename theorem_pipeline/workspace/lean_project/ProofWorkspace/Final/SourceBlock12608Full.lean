import ProofWorkspace.Final.SourceBlock12576Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12608DataFull
import ProofWorkspace.Final.EtaBlock12608Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12608XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12608+k) (sourceBlock12608PiPairs.getD k (0,0))
    (sourceEtaBatch12608Lower k, sourceEtaBatch12608Upper k)
    (sourceBlock12608TwoPairs.getD k (0,0))

theorem sourceBlock12608Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12608XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12608+k):ℂ)).re ∧
      (xi (xiGridArgument (12608+k):ℂ)).re ≤ ((sourceBlock12608XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12608+k) _ _ _
    (sourceBlock12608PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12608_actual_enclosure k hk)
    (sourceBlock12608TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12608Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12608XiPair k).1 := by
  decide +kernel

theorem sourceBlock12608Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12608Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12608XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12608XiPair k)).2 ≤
      sourceBlock12608Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12608_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12608+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12608+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12608Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12608+k) (sourceBlock12608XiPair k) _
    (sourceBlock12608Xi_enclosure k hk) (sourceBlock12608Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12608Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12640_bound (k : ℕ) (hk : k < 12640) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12608
  · exact sourceRoundedMidpoint_first12608_bound k h
  · have hsum : 12608+(k-12608) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12608_bound (k-12608) (by omega)

end ReciprocalXi
