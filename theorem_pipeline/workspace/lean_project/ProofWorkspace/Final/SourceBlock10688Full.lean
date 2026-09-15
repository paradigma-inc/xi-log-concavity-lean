import ProofWorkspace.Final.SourceBlock10656Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10688DataFull
import ProofWorkspace.Final.EtaBlock10688Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10688XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10688+k) (sourceBlock10688PiPairs.getD k (0,0))
    (sourceEtaBatch10688Lower k, sourceEtaBatch10688Upper k)
    (sourceBlock10688TwoPairs.getD k (0,0))

theorem sourceBlock10688Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10688XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10688+k):ℂ)).re ∧
      (xi (xiGridArgument (10688+k):ℂ)).re ≤ ((sourceBlock10688XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10688+k) _ _ _
    (sourceBlock10688PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10688_actual_enclosure k hk)
    (sourceBlock10688TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10688Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10688XiPair k).1 := by
  decide +kernel

theorem sourceBlock10688Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10688Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10688XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10688XiPair k)).2 ≤
      sourceBlock10688Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10688_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10688+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10688+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10688Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10688+k) (sourceBlock10688XiPair k) _
    (sourceBlock10688Xi_enclosure k hk) (sourceBlock10688Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10688Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10720_bound (k : ℕ) (hk : k < 10720) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10688
  · exact sourceRoundedMidpoint_first10688_bound k h
  · have hsum : 10688+(k-10688) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10688_bound (k-10688) (by omega)

end ReciprocalXi
