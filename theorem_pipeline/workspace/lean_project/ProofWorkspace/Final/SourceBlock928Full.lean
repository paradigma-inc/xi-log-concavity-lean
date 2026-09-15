import ProofWorkspace.Final.SourceBlock896Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock928DataFull
import ProofWorkspace.Final.EtaBlock928Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock928XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (928+k) (sourceBlock928PiPairs.getD k (0,0))
    (sourceEtaBatch928Lower k, sourceEtaBatch928Upper k)
    (sourceBlock928TwoPairs.getD k (0,0))

theorem sourceBlock928Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock928XiPair k).1:ℝ) ≤ (xi (xiGridArgument (928+k):ℂ)).re ∧
      (xi (xiGridArgument (928+k):ℂ)).re ≤ ((sourceBlock928XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (928+k) _ _ _
    (sourceBlock928PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch928_actual_enclosure k hk)
    (sourceBlock928TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock928Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock928XiPair k).1 := by
  decide +kernel

theorem sourceBlock928Reciprocal_check : ∀ k : Fin 32,
    sourceBlock928Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock928XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock928XiPair k)).2 ≤
      sourceBlock928Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block928_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((928+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (928+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock928Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (928+k) (sourceBlock928XiPair k) _
    (sourceBlock928Xi_enclosure k hk) (sourceBlock928Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock928Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first960_bound (k : ℕ) (hk : k < 960) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 928
  · exact sourceRoundedMidpoint_first928_bound k h
  · have hsum : 928+(k-928) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block928_bound (k-928) (by omega)

end ReciprocalXi
