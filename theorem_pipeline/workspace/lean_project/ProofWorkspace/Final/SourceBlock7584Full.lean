import ProofWorkspace.Final.SourceBlock7552Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7584DataFull
import ProofWorkspace.Final.EtaBlock7584Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7584XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7584+k) (sourceBlock7584PiPairs.getD k (0,0))
    (sourceEtaBatch7584Lower k, sourceEtaBatch7584Upper k)
    (sourceBlock7584TwoPairs.getD k (0,0))

theorem sourceBlock7584Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7584XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7584+k):ℂ)).re ∧
      (xi (xiGridArgument (7584+k):ℂ)).re ≤ ((sourceBlock7584XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7584+k) _ _ _
    (sourceBlock7584PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7584_actual_enclosure k hk)
    (sourceBlock7584TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7584Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7584XiPair k).1 := by
  decide +kernel

theorem sourceBlock7584Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7584Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7584XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7584XiPair k)).2 ≤
      sourceBlock7584Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7584_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7584+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7584+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7584Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7584+k) (sourceBlock7584XiPair k) _
    (sourceBlock7584Xi_enclosure k hk) (sourceBlock7584Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7584Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7616_bound (k : ℕ) (hk : k < 7616) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7584
  · exact sourceRoundedMidpoint_first7584_bound k h
  · have hsum : 7584+(k-7584) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7584_bound (k-7584) (by omega)

end ReciprocalXi
