import ProofWorkspace.Final.SourceBlock11936Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11968DataFull
import ProofWorkspace.Final.EtaBlock11968Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11968XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11968+k) (sourceBlock11968PiPairs.getD k (0,0))
    (sourceEtaBatch11968Lower k, sourceEtaBatch11968Upper k)
    (sourceBlock11968TwoPairs.getD k (0,0))

theorem sourceBlock11968Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11968XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11968+k):ℂ)).re ∧
      (xi (xiGridArgument (11968+k):ℂ)).re ≤ ((sourceBlock11968XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11968+k) _ _ _
    (sourceBlock11968PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11968_actual_enclosure k hk)
    (sourceBlock11968TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11968Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11968XiPair k).1 := by
  decide +kernel

theorem sourceBlock11968Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11968Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11968XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11968XiPair k)).2 ≤
      sourceBlock11968Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11968_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11968+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11968+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11968Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11968+k) (sourceBlock11968XiPair k) _
    (sourceBlock11968Xi_enclosure k hk) (sourceBlock11968Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11968Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12000_bound (k : ℕ) (hk : k < 12000) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11968
  · exact sourceRoundedMidpoint_first11968_bound k h
  · have hsum : 11968+(k-11968) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11968_bound (k-11968) (by omega)

end ReciprocalXi
