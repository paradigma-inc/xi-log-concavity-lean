import ProofWorkspace.Final.SourceBlock3936Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3968DataFull
import ProofWorkspace.Final.EtaBlock3968Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3968XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3968+k) (sourceBlock3968PiPairs.getD k (0,0))
    (sourceEtaBatch3968Lower k, sourceEtaBatch3968Upper k)
    (sourceBlock3968TwoPairs.getD k (0,0))

theorem sourceBlock3968Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3968XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3968+k):ℂ)).re ∧
      (xi (xiGridArgument (3968+k):ℂ)).re ≤ ((sourceBlock3968XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3968+k) _ _ _
    (sourceBlock3968PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3968_actual_enclosure k hk)
    (sourceBlock3968TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3968Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3968XiPair k).1 := by
  decide +kernel

theorem sourceBlock3968Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3968Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3968XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3968XiPair k)).2 ≤
      sourceBlock3968Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3968_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3968+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3968+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3968Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3968+k) (sourceBlock3968XiPair k) _
    (sourceBlock3968Xi_enclosure k hk) (sourceBlock3968Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3968Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4000_bound (k : ℕ) (hk : k < 4000) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3968
  · exact sourceRoundedMidpoint_first3968_bound k h
  · have hsum : 3968+(k-3968) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3968_bound (k-3968) (by omega)

end ReciprocalXi
