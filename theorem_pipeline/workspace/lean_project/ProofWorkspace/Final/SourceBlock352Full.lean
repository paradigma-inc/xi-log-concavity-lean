import ProofWorkspace.Final.SourceBlock320Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock352DataFull
import ProofWorkspace.Final.EtaBlock352Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock352XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (352+k) (sourceBlock352PiPairs.getD k (0,0))
    (sourceEtaBatch352Lower k, sourceEtaBatch352Upper k)
    (sourceBlock352TwoPairs.getD k (0,0))

theorem sourceBlock352Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock352XiPair k).1:ℝ) ≤ (xi (xiGridArgument (352+k):ℂ)).re ∧
      (xi (xiGridArgument (352+k):ℂ)).re ≤ ((sourceBlock352XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (352+k) _ _ _
    (sourceBlock352PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch352_actual_enclosure k hk)
    (sourceBlock352TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock352Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock352XiPair k).1 := by
  decide +kernel

theorem sourceBlock352Reciprocal_check : ∀ k : Fin 32,
    sourceBlock352Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock352XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock352XiPair k)).2 ≤
      sourceBlock352Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block352_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((352+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (352+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock352Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (352+k) (sourceBlock352XiPair k) _
    (sourceBlock352Xi_enclosure k hk) (sourceBlock352Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock352Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first384_bound (k : ℕ) (hk : k < 384) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 352
  · exact sourceRoundedMidpoint_first352_bound k h
  · have hsum : 352+(k-352) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block352_bound (k-352) (by omega)

end ReciprocalXi
