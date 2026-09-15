import ProofWorkspace.Final.SourceBlock13024Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13056DataFull
import ProofWorkspace.Final.EtaBlock13056Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13056XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13056+k) (sourceBlock13056PiPairs.getD k (0,0))
    (sourceEtaBatch13056Lower k, sourceEtaBatch13056Upper k)
    (sourceBlock13056TwoPairs.getD k (0,0))

theorem sourceBlock13056Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13056XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13056+k):ℂ)).re ∧
      (xi (xiGridArgument (13056+k):ℂ)).re ≤ ((sourceBlock13056XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13056+k) _ _ _
    (sourceBlock13056PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13056_actual_enclosure k hk)
    (sourceBlock13056TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13056Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13056XiPair k).1 := by
  decide +kernel

theorem sourceBlock13056Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13056Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13056XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13056XiPair k)).2 ≤
      sourceBlock13056Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13056_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13056+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13056+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13056Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13056+k) (sourceBlock13056XiPair k) _
    (sourceBlock13056Xi_enclosure k hk) (sourceBlock13056Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13056Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13088_bound (k : ℕ) (hk : k < 13088) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13056
  · exact sourceRoundedMidpoint_first13056_bound k h
  · have hsum : 13056+(k-13056) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13056_bound (k-13056) (by omega)

end ReciprocalXi
