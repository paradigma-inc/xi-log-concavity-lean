import ProofWorkspace.Final.SourceBlock6368Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6400DataFull
import ProofWorkspace.Final.EtaBlock6400Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6400XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6400+k) (sourceBlock6400PiPairs.getD k (0,0))
    (sourceEtaBatch6400Lower k, sourceEtaBatch6400Upper k)
    (sourceBlock6400TwoPairs.getD k (0,0))

theorem sourceBlock6400Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6400XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6400+k):ℂ)).re ∧
      (xi (xiGridArgument (6400+k):ℂ)).re ≤ ((sourceBlock6400XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6400+k) _ _ _
    (sourceBlock6400PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6400_actual_enclosure k hk)
    (sourceBlock6400TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6400Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6400XiPair k).1 := by
  decide +kernel

theorem sourceBlock6400Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6400Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6400XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6400XiPair k)).2 ≤
      sourceBlock6400Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6400_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6400+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6400+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6400Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6400+k) (sourceBlock6400XiPair k) _
    (sourceBlock6400Xi_enclosure k hk) (sourceBlock6400Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6400Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6432_bound (k : ℕ) (hk : k < 6432) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6400
  · exact sourceRoundedMidpoint_first6400_bound k h
  · have hsum : 6400+(k-6400) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6400_bound (k-6400) (by omega)

end ReciprocalXi
