import ProofWorkspace.Final.SourceBlock11648Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11680DataFull
import ProofWorkspace.Final.EtaBlock11680Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11680XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11680+k) (sourceBlock11680PiPairs.getD k (0,0))
    (sourceEtaBatch11680Lower k, sourceEtaBatch11680Upper k)
    (sourceBlock11680TwoPairs.getD k (0,0))

theorem sourceBlock11680Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11680XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11680+k):ℂ)).re ∧
      (xi (xiGridArgument (11680+k):ℂ)).re ≤ ((sourceBlock11680XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11680+k) _ _ _
    (sourceBlock11680PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11680_actual_enclosure k hk)
    (sourceBlock11680TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11680Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11680XiPair k).1 := by
  decide +kernel

theorem sourceBlock11680Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11680Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11680XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11680XiPair k)).2 ≤
      sourceBlock11680Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11680_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11680+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11680+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11680Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11680+k) (sourceBlock11680XiPair k) _
    (sourceBlock11680Xi_enclosure k hk) (sourceBlock11680Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11680Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11712_bound (k : ℕ) (hk : k < 11712) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11680
  · exact sourceRoundedMidpoint_first11680_bound k h
  · have hsum : 11680+(k-11680) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11680_bound (k-11680) (by omega)

end ReciprocalXi
