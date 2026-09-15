import ProofWorkspace.Final.SourceBlock11744Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11776DataFull
import ProofWorkspace.Final.EtaBlock11776Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11776XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11776+k) (sourceBlock11776PiPairs.getD k (0,0))
    (sourceEtaBatch11776Lower k, sourceEtaBatch11776Upper k)
    (sourceBlock11776TwoPairs.getD k (0,0))

theorem sourceBlock11776Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11776XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11776+k):ℂ)).re ∧
      (xi (xiGridArgument (11776+k):ℂ)).re ≤ ((sourceBlock11776XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11776+k) _ _ _
    (sourceBlock11776PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11776_actual_enclosure k hk)
    (sourceBlock11776TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11776Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11776XiPair k).1 := by
  decide +kernel

theorem sourceBlock11776Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11776Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11776XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11776XiPair k)).2 ≤
      sourceBlock11776Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11776_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11776+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11776+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11776Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11776+k) (sourceBlock11776XiPair k) _
    (sourceBlock11776Xi_enclosure k hk) (sourceBlock11776Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11776Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11808_bound (k : ℕ) (hk : k < 11808) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11776
  · exact sourceRoundedMidpoint_first11776_bound k h
  · have hsum : 11776+(k-11776) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11776_bound (k-11776) (by omega)

end ReciprocalXi
