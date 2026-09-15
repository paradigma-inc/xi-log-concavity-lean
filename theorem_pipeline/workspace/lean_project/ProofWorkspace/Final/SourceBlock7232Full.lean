import ProofWorkspace.Final.SourceBlock7200Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7232DataFull
import ProofWorkspace.Final.EtaBlock7232Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7232XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7232+k) (sourceBlock7232PiPairs.getD k (0,0))
    (sourceEtaBatch7232Lower k, sourceEtaBatch7232Upper k)
    (sourceBlock7232TwoPairs.getD k (0,0))

theorem sourceBlock7232Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7232XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7232+k):ℂ)).re ∧
      (xi (xiGridArgument (7232+k):ℂ)).re ≤ ((sourceBlock7232XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7232+k) _ _ _
    (sourceBlock7232PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7232_actual_enclosure k hk)
    (sourceBlock7232TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7232Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7232XiPair k).1 := by
  decide +kernel

theorem sourceBlock7232Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7232Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7232XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7232XiPair k)).2 ≤
      sourceBlock7232Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7232_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7232+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7232+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7232Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7232+k) (sourceBlock7232XiPair k) _
    (sourceBlock7232Xi_enclosure k hk) (sourceBlock7232Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7232Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7264_bound (k : ℕ) (hk : k < 7264) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7232
  · exact sourceRoundedMidpoint_first7232_bound k h
  · have hsum : 7232+(k-7232) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7232_bound (k-7232) (by omega)

end ReciprocalXi
