import ProofWorkspace.Final.SourceBlock5888Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5920DataFull
import ProofWorkspace.Final.EtaBlock5920Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5920XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5920+k) (sourceBlock5920PiPairs.getD k (0,0))
    (sourceEtaBatch5920Lower k, sourceEtaBatch5920Upper k)
    (sourceBlock5920TwoPairs.getD k (0,0))

theorem sourceBlock5920Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5920XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5920+k):ℂ)).re ∧
      (xi (xiGridArgument (5920+k):ℂ)).re ≤ ((sourceBlock5920XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5920+k) _ _ _
    (sourceBlock5920PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5920_actual_enclosure k hk)
    (sourceBlock5920TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5920Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5920XiPair k).1 := by
  decide +kernel

theorem sourceBlock5920Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5920Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5920XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5920XiPair k)).2 ≤
      sourceBlock5920Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5920_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5920+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5920+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5920Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5920+k) (sourceBlock5920XiPair k) _
    (sourceBlock5920Xi_enclosure k hk) (sourceBlock5920Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5920Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5952_bound (k : ℕ) (hk : k < 5952) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5920
  · exact sourceRoundedMidpoint_first5920_bound k h
  · have hsum : 5920+(k-5920) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5920_bound (k-5920) (by omega)

end ReciprocalXi
