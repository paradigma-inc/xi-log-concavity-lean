import ProofWorkspace.Final.SourceBlock4320Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4352DataFull
import ProofWorkspace.Final.EtaBlock4352Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4352XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4352+k) (sourceBlock4352PiPairs.getD k (0,0))
    (sourceEtaBatch4352Lower k, sourceEtaBatch4352Upper k)
    (sourceBlock4352TwoPairs.getD k (0,0))

theorem sourceBlock4352Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4352XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4352+k):ℂ)).re ∧
      (xi (xiGridArgument (4352+k):ℂ)).re ≤ ((sourceBlock4352XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4352+k) _ _ _
    (sourceBlock4352PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4352_actual_enclosure k hk)
    (sourceBlock4352TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4352Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4352XiPair k).1 := by
  decide +kernel

theorem sourceBlock4352Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4352Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4352XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4352XiPair k)).2 ≤
      sourceBlock4352Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4352_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4352+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4352+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4352Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4352+k) (sourceBlock4352XiPair k) _
    (sourceBlock4352Xi_enclosure k hk) (sourceBlock4352Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4352Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4384_bound (k : ℕ) (hk : k < 4384) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4352
  · exact sourceRoundedMidpoint_first4352_bound k h
  · have hsum : 4352+(k-4352) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4352_bound (k-4352) (by omega)

end ReciprocalXi
