import ProofWorkspace.Final.SourceBlock11200Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11232DataFull
import ProofWorkspace.Final.EtaBlock11232Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11232XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11232+k) (sourceBlock11232PiPairs.getD k (0,0))
    (sourceEtaBatch11232Lower k, sourceEtaBatch11232Upper k)
    (sourceBlock11232TwoPairs.getD k (0,0))

theorem sourceBlock11232Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11232XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11232+k):ℂ)).re ∧
      (xi (xiGridArgument (11232+k):ℂ)).re ≤ ((sourceBlock11232XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11232+k) _ _ _
    (sourceBlock11232PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11232_actual_enclosure k hk)
    (sourceBlock11232TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11232Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11232XiPair k).1 := by
  decide +kernel

theorem sourceBlock11232Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11232Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11232XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11232XiPair k)).2 ≤
      sourceBlock11232Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11232_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11232+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11232+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11232Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11232+k) (sourceBlock11232XiPair k) _
    (sourceBlock11232Xi_enclosure k hk) (sourceBlock11232Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11232Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11264_bound (k : ℕ) (hk : k < 11264) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11232
  · exact sourceRoundedMidpoint_first11232_bound k h
  · have hsum : 11232+(k-11232) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11232_bound (k-11232) (by omega)

end ReciprocalXi
