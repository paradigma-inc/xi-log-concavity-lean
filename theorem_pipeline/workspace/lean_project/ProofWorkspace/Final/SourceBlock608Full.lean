import ProofWorkspace.Final.SourceBlock576Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock608DataFull
import ProofWorkspace.Final.EtaBlock608Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock608XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (608+k) (sourceBlock608PiPairs.getD k (0,0))
    (sourceEtaBatch608Lower k, sourceEtaBatch608Upper k)
    (sourceBlock608TwoPairs.getD k (0,0))

theorem sourceBlock608Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock608XiPair k).1:ℝ) ≤ (xi (xiGridArgument (608+k):ℂ)).re ∧
      (xi (xiGridArgument (608+k):ℂ)).re ≤ ((sourceBlock608XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (608+k) _ _ _
    (sourceBlock608PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch608_actual_enclosure k hk)
    (sourceBlock608TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock608Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock608XiPair k).1 := by
  decide +kernel

theorem sourceBlock608Reciprocal_check : ∀ k : Fin 32,
    sourceBlock608Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock608XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock608XiPair k)).2 ≤
      sourceBlock608Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block608_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((608+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (608+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock608Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (608+k) (sourceBlock608XiPair k) _
    (sourceBlock608Xi_enclosure k hk) (sourceBlock608Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock608Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first640_bound (k : ℕ) (hk : k < 640) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 608
  · exact sourceRoundedMidpoint_first608_bound k h
  · have hsum : 608+(k-608) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block608_bound (k-608) (by omega)

end ReciprocalXi
