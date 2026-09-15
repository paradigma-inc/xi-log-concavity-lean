import ProofWorkspace.Final.SourceBlock6848Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6880DataFull
import ProofWorkspace.Final.EtaBlock6880Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6880XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6880+k) (sourceBlock6880PiPairs.getD k (0,0))
    (sourceEtaBatch6880Lower k, sourceEtaBatch6880Upper k)
    (sourceBlock6880TwoPairs.getD k (0,0))

theorem sourceBlock6880Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6880XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6880+k):ℂ)).re ∧
      (xi (xiGridArgument (6880+k):ℂ)).re ≤ ((sourceBlock6880XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6880+k) _ _ _
    (sourceBlock6880PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6880_actual_enclosure k hk)
    (sourceBlock6880TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6880Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6880XiPair k).1 := by
  decide +kernel

theorem sourceBlock6880Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6880Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6880XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6880XiPair k)).2 ≤
      sourceBlock6880Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6880_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6880+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6880+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6880Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6880+k) (sourceBlock6880XiPair k) _
    (sourceBlock6880Xi_enclosure k hk) (sourceBlock6880Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6880Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6912_bound (k : ℕ) (hk : k < 6912) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6880
  · exact sourceRoundedMidpoint_first6880_bound k h
  · have hsum : 6880+(k-6880) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6880_bound (k-6880) (by omega)

end ReciprocalXi
