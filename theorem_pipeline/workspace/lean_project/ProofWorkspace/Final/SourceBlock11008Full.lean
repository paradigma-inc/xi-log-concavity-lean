import ProofWorkspace.Final.SourceBlock10976Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11008DataFull
import ProofWorkspace.Final.EtaBlock11008Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11008XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11008+k) (sourceBlock11008PiPairs.getD k (0,0))
    (sourceEtaBatch11008Lower k, sourceEtaBatch11008Upper k)
    (sourceBlock11008TwoPairs.getD k (0,0))

theorem sourceBlock11008Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11008XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11008+k):ℂ)).re ∧
      (xi (xiGridArgument (11008+k):ℂ)).re ≤ ((sourceBlock11008XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11008+k) _ _ _
    (sourceBlock11008PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11008_actual_enclosure k hk)
    (sourceBlock11008TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11008Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11008XiPair k).1 := by
  decide +kernel

theorem sourceBlock11008Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11008Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11008XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11008XiPair k)).2 ≤
      sourceBlock11008Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11008_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11008+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11008+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11008Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11008+k) (sourceBlock11008XiPair k) _
    (sourceBlock11008Xi_enclosure k hk) (sourceBlock11008Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11008Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11040_bound (k : ℕ) (hk : k < 11040) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11008
  · exact sourceRoundedMidpoint_first11008_bound k h
  · have hsum : 11008+(k-11008) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11008_bound (k-11008) (by omega)

end ReciprocalXi
