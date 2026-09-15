import ProofWorkspace.Final.SourceBlock1792Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1824DataFull
import ProofWorkspace.Final.EtaBlock1824Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1824XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1824+k) (sourceBlock1824PiPairs.getD k (0,0))
    (sourceEtaBatch1824Lower k, sourceEtaBatch1824Upper k)
    (sourceBlock1824TwoPairs.getD k (0,0))

theorem sourceBlock1824Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1824XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1824+k):ℂ)).re ∧
      (xi (xiGridArgument (1824+k):ℂ)).re ≤ ((sourceBlock1824XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1824+k) _ _ _
    (sourceBlock1824PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1824_actual_enclosure k hk)
    (sourceBlock1824TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1824Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1824XiPair k).1 := by
  decide +kernel

theorem sourceBlock1824Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1824Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1824XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1824XiPair k)).2 ≤
      sourceBlock1824Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1824_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1824+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1824+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1824Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1824+k) (sourceBlock1824XiPair k) _
    (sourceBlock1824Xi_enclosure k hk) (sourceBlock1824Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1824Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1856_bound (k : ℕ) (hk : k < 1856) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1824
  · exact sourceRoundedMidpoint_first1824_bound k h
  · have hsum : 1824+(k-1824) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1824_bound (k-1824) (by omega)

end ReciprocalXi
