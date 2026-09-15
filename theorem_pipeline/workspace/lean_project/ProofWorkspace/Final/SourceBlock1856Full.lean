import ProofWorkspace.Final.SourceBlock1824Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1856DataFull
import ProofWorkspace.Final.EtaBlock1856Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1856XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1856+k) (sourceBlock1856PiPairs.getD k (0,0))
    (sourceEtaBatch1856Lower k, sourceEtaBatch1856Upper k)
    (sourceBlock1856TwoPairs.getD k (0,0))

theorem sourceBlock1856Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1856XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1856+k):ℂ)).re ∧
      (xi (xiGridArgument (1856+k):ℂ)).re ≤ ((sourceBlock1856XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1856+k) _ _ _
    (sourceBlock1856PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1856_actual_enclosure k hk)
    (sourceBlock1856TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1856Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1856XiPair k).1 := by
  decide +kernel

theorem sourceBlock1856Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1856Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1856XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1856XiPair k)).2 ≤
      sourceBlock1856Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1856_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1856+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1856+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1856Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1856+k) (sourceBlock1856XiPair k) _
    (sourceBlock1856Xi_enclosure k hk) (sourceBlock1856Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1856Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1888_bound (k : ℕ) (hk : k < 1888) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1856
  · exact sourceRoundedMidpoint_first1856_bound k h
  · have hsum : 1856+(k-1856) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1856_bound (k-1856) (by omega)

end ReciprocalXi
