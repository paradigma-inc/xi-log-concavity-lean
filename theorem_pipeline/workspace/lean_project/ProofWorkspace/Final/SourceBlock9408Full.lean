import ProofWorkspace.Final.SourceBlock9376Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9408DataFull
import ProofWorkspace.Final.EtaBlock9408Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9408XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9408+k) (sourceBlock9408PiPairs.getD k (0,0))
    (sourceEtaBatch9408Lower k, sourceEtaBatch9408Upper k)
    (sourceBlock9408TwoPairs.getD k (0,0))

theorem sourceBlock9408Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9408XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9408+k):ℂ)).re ∧
      (xi (xiGridArgument (9408+k):ℂ)).re ≤ ((sourceBlock9408XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9408+k) _ _ _
    (sourceBlock9408PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9408_actual_enclosure k hk)
    (sourceBlock9408TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9408Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9408XiPair k).1 := by
  decide +kernel

theorem sourceBlock9408Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9408Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9408XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9408XiPair k)).2 ≤
      sourceBlock9408Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9408_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9408+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9408+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9408Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9408+k) (sourceBlock9408XiPair k) _
    (sourceBlock9408Xi_enclosure k hk) (sourceBlock9408Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9408Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9440_bound (k : ℕ) (hk : k < 9440) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9408
  · exact sourceRoundedMidpoint_first9408_bound k h
  · have hsum : 9408+(k-9408) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9408_bound (k-9408) (by omega)

end ReciprocalXi
