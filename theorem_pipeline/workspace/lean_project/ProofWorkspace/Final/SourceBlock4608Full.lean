import ProofWorkspace.Final.SourceBlock4576Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4608DataFull
import ProofWorkspace.Final.EtaBlock4608Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4608XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4608+k) (sourceBlock4608PiPairs.getD k (0,0))
    (sourceEtaBatch4608Lower k, sourceEtaBatch4608Upper k)
    (sourceBlock4608TwoPairs.getD k (0,0))

theorem sourceBlock4608Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4608XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4608+k):ℂ)).re ∧
      (xi (xiGridArgument (4608+k):ℂ)).re ≤ ((sourceBlock4608XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4608+k) _ _ _
    (sourceBlock4608PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4608_actual_enclosure k hk)
    (sourceBlock4608TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4608Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4608XiPair k).1 := by
  decide +kernel

theorem sourceBlock4608Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4608Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4608XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4608XiPair k)).2 ≤
      sourceBlock4608Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4608_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4608+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4608+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4608Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4608+k) (sourceBlock4608XiPair k) _
    (sourceBlock4608Xi_enclosure k hk) (sourceBlock4608Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4608Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4640_bound (k : ℕ) (hk : k < 4640) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4608
  · exact sourceRoundedMidpoint_first4608_bound k h
  · have hsum : 4608+(k-4608) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4608_bound (k-4608) (by omega)

end ReciprocalXi
