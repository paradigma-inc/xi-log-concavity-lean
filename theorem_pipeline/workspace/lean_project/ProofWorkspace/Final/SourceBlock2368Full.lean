import ProofWorkspace.Final.SourceBlock2336Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock2368DataFull
import ProofWorkspace.Final.EtaBlock2368Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock2368XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (2368+k) (sourceBlock2368PiPairs.getD k (0,0))
    (sourceEtaBatch2368Lower k, sourceEtaBatch2368Upper k)
    (sourceBlock2368TwoPairs.getD k (0,0))

theorem sourceBlock2368Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock2368XiPair k).1:ℝ) ≤ (xi (xiGridArgument (2368+k):ℂ)).re ∧
      (xi (xiGridArgument (2368+k):ℂ)).re ≤ ((sourceBlock2368XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (2368+k) _ _ _
    (sourceBlock2368PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch2368_actual_enclosure k hk)
    (sourceBlock2368TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock2368Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock2368XiPair k).1 := by
  decide +kernel

theorem sourceBlock2368Reciprocal_check : ∀ k : Fin 32,
    sourceBlock2368Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock2368XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock2368XiPair k)).2 ≤
      sourceBlock2368Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block2368_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((2368+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (2368+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock2368Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (2368+k) (sourceBlock2368XiPair k) _
    (sourceBlock2368Xi_enclosure k hk) (sourceBlock2368Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock2368Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2400_bound (k : ℕ) (hk : k < 2400) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 2368
  · exact sourceRoundedMidpoint_first2368_bound k h
  · have hsum : 2368+(k-2368) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block2368_bound (k-2368) (by omega)

end ReciprocalXi
