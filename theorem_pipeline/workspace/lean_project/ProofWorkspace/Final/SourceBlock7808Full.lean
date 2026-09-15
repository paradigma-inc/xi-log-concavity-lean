import ProofWorkspace.Final.SourceBlock7776Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7808DataFull
import ProofWorkspace.Final.EtaBlock7808Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7808XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7808+k) (sourceBlock7808PiPairs.getD k (0,0))
    (sourceEtaBatch7808Lower k, sourceEtaBatch7808Upper k)
    (sourceBlock7808TwoPairs.getD k (0,0))

theorem sourceBlock7808Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7808XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7808+k):ℂ)).re ∧
      (xi (xiGridArgument (7808+k):ℂ)).re ≤ ((sourceBlock7808XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7808+k) _ _ _
    (sourceBlock7808PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7808_actual_enclosure k hk)
    (sourceBlock7808TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7808Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7808XiPair k).1 := by
  decide +kernel

theorem sourceBlock7808Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7808Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7808XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7808XiPair k)).2 ≤
      sourceBlock7808Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7808_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7808+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7808+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7808Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7808+k) (sourceBlock7808XiPair k) _
    (sourceBlock7808Xi_enclosure k hk) (sourceBlock7808Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7808Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7840_bound (k : ℕ) (hk : k < 7840) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7808
  · exact sourceRoundedMidpoint_first7808_bound k h
  · have hsum : 7808+(k-7808) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7808_bound (k-7808) (by omega)

end ReciprocalXi
