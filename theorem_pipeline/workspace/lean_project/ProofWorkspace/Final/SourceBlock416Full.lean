import ProofWorkspace.Final.SourceBlock384Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock416DataFull
import ProofWorkspace.Final.EtaBlock416Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock416XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (416+k) (sourceBlock416PiPairs.getD k (0,0))
    (sourceEtaBatch416Lower k, sourceEtaBatch416Upper k)
    (sourceBlock416TwoPairs.getD k (0,0))

theorem sourceBlock416Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock416XiPair k).1:ℝ) ≤ (xi (xiGridArgument (416+k):ℂ)).re ∧
      (xi (xiGridArgument (416+k):ℂ)).re ≤ ((sourceBlock416XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (416+k) _ _ _
    (sourceBlock416PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch416_actual_enclosure k hk)
    (sourceBlock416TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock416Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock416XiPair k).1 := by
  decide +kernel

theorem sourceBlock416Reciprocal_check : ∀ k : Fin 32,
    sourceBlock416Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock416XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock416XiPair k)).2 ≤
      sourceBlock416Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block416_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((416+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (416+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock416Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (416+k) (sourceBlock416XiPair k) _
    (sourceBlock416Xi_enclosure k hk) (sourceBlock416Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock416Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first448_bound (k : ℕ) (hk : k < 448) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 416
  · exact sourceRoundedMidpoint_first416_bound k h
  · have hsum : 416+(k-416) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block416_bound (k-416) (by omega)

end ReciprocalXi
