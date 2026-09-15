import ProofWorkspace.Final.SourceBlock8896Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8928DataFull
import ProofWorkspace.Final.EtaBlock8928Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8928XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8928+k) (sourceBlock8928PiPairs.getD k (0,0))
    (sourceEtaBatch8928Lower k, sourceEtaBatch8928Upper k)
    (sourceBlock8928TwoPairs.getD k (0,0))

theorem sourceBlock8928Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8928XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8928+k):ℂ)).re ∧
      (xi (xiGridArgument (8928+k):ℂ)).re ≤ ((sourceBlock8928XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8928+k) _ _ _
    (sourceBlock8928PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8928_actual_enclosure k hk)
    (sourceBlock8928TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8928Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8928XiPair k).1 := by
  decide +kernel

theorem sourceBlock8928Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8928Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8928XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8928XiPair k)).2 ≤
      sourceBlock8928Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8928_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8928+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8928+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8928Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8928+k) (sourceBlock8928XiPair k) _
    (sourceBlock8928Xi_enclosure k hk) (sourceBlock8928Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8928Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8960_bound (k : ℕ) (hk : k < 8960) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8928
  · exact sourceRoundedMidpoint_first8928_bound k h
  · have hsum : 8928+(k-8928) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8928_bound (k-8928) (by omega)

end ReciprocalXi
