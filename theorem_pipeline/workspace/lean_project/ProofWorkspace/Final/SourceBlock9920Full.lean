import ProofWorkspace.Final.SourceBlock9888Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9920DataFull
import ProofWorkspace.Final.EtaBlock9920Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9920XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9920+k) (sourceBlock9920PiPairs.getD k (0,0))
    (sourceEtaBatch9920Lower k, sourceEtaBatch9920Upper k)
    (sourceBlock9920TwoPairs.getD k (0,0))

theorem sourceBlock9920Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9920XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9920+k):ℂ)).re ∧
      (xi (xiGridArgument (9920+k):ℂ)).re ≤ ((sourceBlock9920XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9920+k) _ _ _
    (sourceBlock9920PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9920_actual_enclosure k hk)
    (sourceBlock9920TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9920Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9920XiPair k).1 := by
  decide +kernel

theorem sourceBlock9920Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9920Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9920XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9920XiPair k)).2 ≤
      sourceBlock9920Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9920_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9920+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9920+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9920Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9920+k) (sourceBlock9920XiPair k) _
    (sourceBlock9920Xi_enclosure k hk) (sourceBlock9920Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9920Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9952_bound (k : ℕ) (hk : k < 9952) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9920
  · exact sourceRoundedMidpoint_first9920_bound k h
  · have hsum : 9920+(k-9920) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9920_bound (k-9920) (by omega)

end ReciprocalXi
