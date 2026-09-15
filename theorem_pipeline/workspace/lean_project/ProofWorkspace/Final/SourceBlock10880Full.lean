import ProofWorkspace.Final.SourceBlock10848Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10880DataFull
import ProofWorkspace.Final.EtaBlock10880Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10880XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10880+k) (sourceBlock10880PiPairs.getD k (0,0))
    (sourceEtaBatch10880Lower k, sourceEtaBatch10880Upper k)
    (sourceBlock10880TwoPairs.getD k (0,0))

theorem sourceBlock10880Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10880XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10880+k):ℂ)).re ∧
      (xi (xiGridArgument (10880+k):ℂ)).re ≤ ((sourceBlock10880XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10880+k) _ _ _
    (sourceBlock10880PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10880_actual_enclosure k hk)
    (sourceBlock10880TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10880Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10880XiPair k).1 := by
  decide +kernel

theorem sourceBlock10880Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10880Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10880XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10880XiPair k)).2 ≤
      sourceBlock10880Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10880_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10880+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10880+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10880Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10880+k) (sourceBlock10880XiPair k) _
    (sourceBlock10880Xi_enclosure k hk) (sourceBlock10880Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10880Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10912_bound (k : ℕ) (hk : k < 10912) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10880
  · exact sourceRoundedMidpoint_first10880_bound k h
  · have hsum : 10880+(k-10880) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10880_bound (k-10880) (by omega)

end ReciprocalXi
