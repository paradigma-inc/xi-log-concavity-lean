import ProofWorkspace.Final.SourceBlock7936Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7968DataFull
import ProofWorkspace.Final.EtaBlock7968Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7968XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7968+k) (sourceBlock7968PiPairs.getD k (0,0))
    (sourceEtaBatch7968Lower k, sourceEtaBatch7968Upper k)
    (sourceBlock7968TwoPairs.getD k (0,0))

theorem sourceBlock7968Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7968XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7968+k):ℂ)).re ∧
      (xi (xiGridArgument (7968+k):ℂ)).re ≤ ((sourceBlock7968XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7968+k) _ _ _
    (sourceBlock7968PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7968_actual_enclosure k hk)
    (sourceBlock7968TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7968Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7968XiPair k).1 := by
  decide +kernel

theorem sourceBlock7968Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7968Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7968XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7968XiPair k)).2 ≤
      sourceBlock7968Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7968_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7968+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7968+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7968Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7968+k) (sourceBlock7968XiPair k) _
    (sourceBlock7968Xi_enclosure k hk) (sourceBlock7968Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7968Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8000_bound (k : ℕ) (hk : k < 8000) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7968
  · exact sourceRoundedMidpoint_first7968_bound k h
  · have hsum : 7968+(k-7968) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7968_bound (k-7968) (by omega)

end ReciprocalXi
