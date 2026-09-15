import ProofWorkspace.Final.SourceBlock1568Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1600DataFull
import ProofWorkspace.Final.EtaBlock1600Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1600XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1600+k) (sourceBlock1600PiPairs.getD k (0,0))
    (sourceEtaBatch1600Lower k, sourceEtaBatch1600Upper k)
    (sourceBlock1600TwoPairs.getD k (0,0))

theorem sourceBlock1600Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1600XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1600+k):ℂ)).re ∧
      (xi (xiGridArgument (1600+k):ℂ)).re ≤ ((sourceBlock1600XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1600+k) _ _ _
    (sourceBlock1600PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1600_actual_enclosure k hk)
    (sourceBlock1600TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1600Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1600XiPair k).1 := by
  decide +kernel

theorem sourceBlock1600Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1600Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1600XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1600XiPair k)).2 ≤
      sourceBlock1600Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1600_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1600+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1600+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1600Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1600+k) (sourceBlock1600XiPair k) _
    (sourceBlock1600Xi_enclosure k hk) (sourceBlock1600Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1600Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1632_bound (k : ℕ) (hk : k < 1632) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1600
  · exact sourceRoundedMidpoint_first1600_bound k h
  · have hsum : 1600+(k-1600) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1600_bound (k-1600) (by omega)

end ReciprocalXi
