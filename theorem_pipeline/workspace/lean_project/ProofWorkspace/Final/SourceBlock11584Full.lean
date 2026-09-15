import ProofWorkspace.Final.SourceBlock11552Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11584DataFull
import ProofWorkspace.Final.EtaBlock11584Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11584XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11584+k) (sourceBlock11584PiPairs.getD k (0,0))
    (sourceEtaBatch11584Lower k, sourceEtaBatch11584Upper k)
    (sourceBlock11584TwoPairs.getD k (0,0))

theorem sourceBlock11584Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11584XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11584+k):ℂ)).re ∧
      (xi (xiGridArgument (11584+k):ℂ)).re ≤ ((sourceBlock11584XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11584+k) _ _ _
    (sourceBlock11584PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11584_actual_enclosure k hk)
    (sourceBlock11584TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11584Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11584XiPair k).1 := by
  decide +kernel

theorem sourceBlock11584Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11584Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11584XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11584XiPair k)).2 ≤
      sourceBlock11584Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11584_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11584+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11584+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11584Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11584+k) (sourceBlock11584XiPair k) _
    (sourceBlock11584Xi_enclosure k hk) (sourceBlock11584Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11584Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11616_bound (k : ℕ) (hk : k < 11616) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11584
  · exact sourceRoundedMidpoint_first11584_bound k h
  · have hsum : 11584+(k-11584) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11584_bound (k-11584) (by omega)

end ReciprocalXi
