import ProofWorkspace.Final.SourceBlock12320Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12352DataFull
import ProofWorkspace.Final.EtaBlock12352Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12352XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12352+k) (sourceBlock12352PiPairs.getD k (0,0))
    (sourceEtaBatch12352Lower k, sourceEtaBatch12352Upper k)
    (sourceBlock12352TwoPairs.getD k (0,0))

theorem sourceBlock12352Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12352XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12352+k):ℂ)).re ∧
      (xi (xiGridArgument (12352+k):ℂ)).re ≤ ((sourceBlock12352XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12352+k) _ _ _
    (sourceBlock12352PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12352_actual_enclosure k hk)
    (sourceBlock12352TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12352Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12352XiPair k).1 := by
  decide +kernel

theorem sourceBlock12352Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12352Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12352XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12352XiPair k)).2 ≤
      sourceBlock12352Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12352_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12352+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12352+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12352Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12352+k) (sourceBlock12352XiPair k) _
    (sourceBlock12352Xi_enclosure k hk) (sourceBlock12352Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12352Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12384_bound (k : ℕ) (hk : k < 12384) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12352
  · exact sourceRoundedMidpoint_first12352_bound k h
  · have hsum : 12352+(k-12352) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12352_bound (k-12352) (by omega)

end ReciprocalXi
