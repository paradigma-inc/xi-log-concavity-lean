import ProofWorkspace.Final.SourceBlock11680Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11712DataFull
import ProofWorkspace.Final.EtaBlock11712Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11712XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11712+k) (sourceBlock11712PiPairs.getD k (0,0))
    (sourceEtaBatch11712Lower k, sourceEtaBatch11712Upper k)
    (sourceBlock11712TwoPairs.getD k (0,0))

theorem sourceBlock11712Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11712XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11712+k):ℂ)).re ∧
      (xi (xiGridArgument (11712+k):ℂ)).re ≤ ((sourceBlock11712XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11712+k) _ _ _
    (sourceBlock11712PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11712_actual_enclosure k hk)
    (sourceBlock11712TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11712Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11712XiPair k).1 := by
  decide +kernel

theorem sourceBlock11712Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11712Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11712XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11712XiPair k)).2 ≤
      sourceBlock11712Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11712_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11712+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11712+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11712Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11712+k) (sourceBlock11712XiPair k) _
    (sourceBlock11712Xi_enclosure k hk) (sourceBlock11712Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11712Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11744_bound (k : ℕ) (hk : k < 11744) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11712
  · exact sourceRoundedMidpoint_first11712_bound k h
  · have hsum : 11712+(k-11712) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11712_bound (k-11712) (by omega)

end ReciprocalXi
