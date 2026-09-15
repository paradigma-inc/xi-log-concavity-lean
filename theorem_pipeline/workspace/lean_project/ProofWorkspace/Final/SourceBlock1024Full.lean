import ProofWorkspace.Final.SourceBlock992Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1024DataFull
import ProofWorkspace.Final.EtaBlock1024Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1024XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1024+k) (sourceBlock1024PiPairs.getD k (0,0))
    (sourceEtaBatch1024Lower k, sourceEtaBatch1024Upper k)
    (sourceBlock1024TwoPairs.getD k (0,0))

theorem sourceBlock1024Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1024XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1024+k):ℂ)).re ∧
      (xi (xiGridArgument (1024+k):ℂ)).re ≤ ((sourceBlock1024XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1024+k) _ _ _
    (sourceBlock1024PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1024_actual_enclosure k hk)
    (sourceBlock1024TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1024Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1024XiPair k).1 := by
  decide +kernel

theorem sourceBlock1024Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1024Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1024XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1024XiPair k)).2 ≤
      sourceBlock1024Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1024_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1024+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1024+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1024Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1024+k) (sourceBlock1024XiPair k) _
    (sourceBlock1024Xi_enclosure k hk) (sourceBlock1024Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1024Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1056_bound (k : ℕ) (hk : k < 1056) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1024
  · exact sourceRoundedMidpoint_first1024_bound k h
  · have hsum : 1024+(k-1024) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1024_bound (k-1024) (by omega)

end ReciprocalXi
