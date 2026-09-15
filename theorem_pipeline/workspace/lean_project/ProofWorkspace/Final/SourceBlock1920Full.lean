import ProofWorkspace.Final.SourceBlock1888Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1920DataFull
import ProofWorkspace.Final.EtaBlock1920Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1920XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1920+k) (sourceBlock1920PiPairs.getD k (0,0))
    (sourceEtaBatch1920Lower k, sourceEtaBatch1920Upper k)
    (sourceBlock1920TwoPairs.getD k (0,0))

theorem sourceBlock1920Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1920XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1920+k):ℂ)).re ∧
      (xi (xiGridArgument (1920+k):ℂ)).re ≤ ((sourceBlock1920XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1920+k) _ _ _
    (sourceBlock1920PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1920_actual_enclosure k hk)
    (sourceBlock1920TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1920Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1920XiPair k).1 := by
  decide +kernel

theorem sourceBlock1920Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1920Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1920XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1920XiPair k)).2 ≤
      sourceBlock1920Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1920_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1920+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1920+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1920Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1920+k) (sourceBlock1920XiPair k) _
    (sourceBlock1920Xi_enclosure k hk) (sourceBlock1920Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1920Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1952_bound (k : ℕ) (hk : k < 1952) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1920
  · exact sourceRoundedMidpoint_first1920_bound k h
  · have hsum : 1920+(k-1920) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1920_bound (k-1920) (by omega)

end ReciprocalXi
