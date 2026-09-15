import ProofWorkspace.Final.SourceBlock4384Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4416DataFull
import ProofWorkspace.Final.EtaBlock4416Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4416XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4416+k) (sourceBlock4416PiPairs.getD k (0,0))
    (sourceEtaBatch4416Lower k, sourceEtaBatch4416Upper k)
    (sourceBlock4416TwoPairs.getD k (0,0))

theorem sourceBlock4416Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4416XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4416+k):ℂ)).re ∧
      (xi (xiGridArgument (4416+k):ℂ)).re ≤ ((sourceBlock4416XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4416+k) _ _ _
    (sourceBlock4416PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4416_actual_enclosure k hk)
    (sourceBlock4416TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4416Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4416XiPair k).1 := by
  decide +kernel

theorem sourceBlock4416Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4416Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4416XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4416XiPair k)).2 ≤
      sourceBlock4416Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4416_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4416+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4416+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4416Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4416+k) (sourceBlock4416XiPair k) _
    (sourceBlock4416Xi_enclosure k hk) (sourceBlock4416Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4416Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4448_bound (k : ℕ) (hk : k < 4448) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4416
  · exact sourceRoundedMidpoint_first4416_bound k h
  · have hsum : 4416+(k-4416) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4416_bound (k-4416) (by omega)

end ReciprocalXi
