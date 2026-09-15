import ProofWorkspace.Final.SourceBlock7744Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7776DataFull
import ProofWorkspace.Final.EtaBlock7776Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7776XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7776+k) (sourceBlock7776PiPairs.getD k (0,0))
    (sourceEtaBatch7776Lower k, sourceEtaBatch7776Upper k)
    (sourceBlock7776TwoPairs.getD k (0,0))

theorem sourceBlock7776Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7776XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7776+k):ℂ)).re ∧
      (xi (xiGridArgument (7776+k):ℂ)).re ≤ ((sourceBlock7776XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7776+k) _ _ _
    (sourceBlock7776PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7776_actual_enclosure k hk)
    (sourceBlock7776TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7776Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7776XiPair k).1 := by
  decide +kernel

theorem sourceBlock7776Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7776Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7776XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7776XiPair k)).2 ≤
      sourceBlock7776Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7776_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7776+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7776+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7776Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7776+k) (sourceBlock7776XiPair k) _
    (sourceBlock7776Xi_enclosure k hk) (sourceBlock7776Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7776Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7808_bound (k : ℕ) (hk : k < 7808) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7776
  · exact sourceRoundedMidpoint_first7776_bound k h
  · have hsum : 7776+(k-7776) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7776_bound (k-7776) (by omega)

end ReciprocalXi
