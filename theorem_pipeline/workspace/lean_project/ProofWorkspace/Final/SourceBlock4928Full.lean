import ProofWorkspace.Final.SourceBlock4896Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4928DataFull
import ProofWorkspace.Final.EtaBlock4928Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4928XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4928+k) (sourceBlock4928PiPairs.getD k (0,0))
    (sourceEtaBatch4928Lower k, sourceEtaBatch4928Upper k)
    (sourceBlock4928TwoPairs.getD k (0,0))

theorem sourceBlock4928Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4928XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4928+k):ℂ)).re ∧
      (xi (xiGridArgument (4928+k):ℂ)).re ≤ ((sourceBlock4928XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4928+k) _ _ _
    (sourceBlock4928PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4928_actual_enclosure k hk)
    (sourceBlock4928TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4928Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4928XiPair k).1 := by
  decide +kernel

theorem sourceBlock4928Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4928Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4928XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4928XiPair k)).2 ≤
      sourceBlock4928Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4928_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4928+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4928+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4928Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4928+k) (sourceBlock4928XiPair k) _
    (sourceBlock4928Xi_enclosure k hk) (sourceBlock4928Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4928Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4960_bound (k : ℕ) (hk : k < 4960) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4928
  · exact sourceRoundedMidpoint_first4928_bound k h
  · have hsum : 4928+(k-4928) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4928_bound (k-4928) (by omega)

end ReciprocalXi
