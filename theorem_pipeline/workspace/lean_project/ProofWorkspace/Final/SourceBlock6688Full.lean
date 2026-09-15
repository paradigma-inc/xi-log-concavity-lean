import ProofWorkspace.Final.SourceBlock6656Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6688DataFull
import ProofWorkspace.Final.EtaBlock6688Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6688XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6688+k) (sourceBlock6688PiPairs.getD k (0,0))
    (sourceEtaBatch6688Lower k, sourceEtaBatch6688Upper k)
    (sourceBlock6688TwoPairs.getD k (0,0))

theorem sourceBlock6688Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6688XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6688+k):ℂ)).re ∧
      (xi (xiGridArgument (6688+k):ℂ)).re ≤ ((sourceBlock6688XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6688+k) _ _ _
    (sourceBlock6688PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6688_actual_enclosure k hk)
    (sourceBlock6688TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6688Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6688XiPair k).1 := by
  decide +kernel

theorem sourceBlock6688Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6688Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6688XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6688XiPair k)).2 ≤
      sourceBlock6688Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6688_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6688+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6688+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6688Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6688+k) (sourceBlock6688XiPair k) _
    (sourceBlock6688Xi_enclosure k hk) (sourceBlock6688Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6688Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6720_bound (k : ℕ) (hk : k < 6720) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6688
  · exact sourceRoundedMidpoint_first6688_bound k h
  · have hsum : 6688+(k-6688) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6688_bound (k-6688) (by omega)

end ReciprocalXi
