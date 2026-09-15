import ProofWorkspace.Final.SourceBlock5024Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5056DataFull
import ProofWorkspace.Final.EtaBlock5056Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5056XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5056+k) (sourceBlock5056PiPairs.getD k (0,0))
    (sourceEtaBatch5056Lower k, sourceEtaBatch5056Upper k)
    (sourceBlock5056TwoPairs.getD k (0,0))

theorem sourceBlock5056Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5056XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5056+k):ℂ)).re ∧
      (xi (xiGridArgument (5056+k):ℂ)).re ≤ ((sourceBlock5056XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5056+k) _ _ _
    (sourceBlock5056PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5056_actual_enclosure k hk)
    (sourceBlock5056TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5056Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5056XiPair k).1 := by
  decide +kernel

theorem sourceBlock5056Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5056Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5056XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5056XiPair k)).2 ≤
      sourceBlock5056Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5056_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5056+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5056+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5056Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5056+k) (sourceBlock5056XiPair k) _
    (sourceBlock5056Xi_enclosure k hk) (sourceBlock5056Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5056Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5088_bound (k : ℕ) (hk : k < 5088) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5056
  · exact sourceRoundedMidpoint_first5056_bound k h
  · have hsum : 5056+(k-5056) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5056_bound (k-5056) (by omega)

end ReciprocalXi
