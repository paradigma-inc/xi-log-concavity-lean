import ProofWorkspace.Final.SourceBlock12896Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12928DataFull
import ProofWorkspace.Final.EtaBlock12928Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12928XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12928+k) (sourceBlock12928PiPairs.getD k (0,0))
    (sourceEtaBatch12928Lower k, sourceEtaBatch12928Upper k)
    (sourceBlock12928TwoPairs.getD k (0,0))

theorem sourceBlock12928Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12928XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12928+k):ℂ)).re ∧
      (xi (xiGridArgument (12928+k):ℂ)).re ≤ ((sourceBlock12928XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12928+k) _ _ _
    (sourceBlock12928PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12928_actual_enclosure k hk)
    (sourceBlock12928TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12928Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12928XiPair k).1 := by
  decide +kernel

theorem sourceBlock12928Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12928Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12928XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12928XiPair k)).2 ≤
      sourceBlock12928Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12928_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12928+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12928+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12928Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12928+k) (sourceBlock12928XiPair k) _
    (sourceBlock12928Xi_enclosure k hk) (sourceBlock12928Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12928Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12960_bound (k : ℕ) (hk : k < 12960) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12928
  · exact sourceRoundedMidpoint_first12928_bound k h
  · have hsum : 12928+(k-12928) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12928_bound (k-12928) (by omega)

end ReciprocalXi
