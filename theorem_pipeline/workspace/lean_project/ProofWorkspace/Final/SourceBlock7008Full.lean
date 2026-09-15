import ProofWorkspace.Final.SourceBlock6976Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7008DataFull
import ProofWorkspace.Final.EtaBlock7008Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7008XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7008+k) (sourceBlock7008PiPairs.getD k (0,0))
    (sourceEtaBatch7008Lower k, sourceEtaBatch7008Upper k)
    (sourceBlock7008TwoPairs.getD k (0,0))

theorem sourceBlock7008Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7008XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7008+k):ℂ)).re ∧
      (xi (xiGridArgument (7008+k):ℂ)).re ≤ ((sourceBlock7008XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7008+k) _ _ _
    (sourceBlock7008PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7008_actual_enclosure k hk)
    (sourceBlock7008TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7008Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7008XiPair k).1 := by
  decide +kernel

theorem sourceBlock7008Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7008Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7008XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7008XiPair k)).2 ≤
      sourceBlock7008Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7008_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7008+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7008+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7008Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7008+k) (sourceBlock7008XiPair k) _
    (sourceBlock7008Xi_enclosure k hk) (sourceBlock7008Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7008Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7040_bound (k : ℕ) (hk : k < 7040) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7008
  · exact sourceRoundedMidpoint_first7008_bound k h
  · have hsum : 7008+(k-7008) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7008_bound (k-7008) (by omega)

end ReciprocalXi
