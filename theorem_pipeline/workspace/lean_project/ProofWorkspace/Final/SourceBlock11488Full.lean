import ProofWorkspace.Final.SourceBlock11456Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11488DataFull
import ProofWorkspace.Final.EtaBlock11488Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11488XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11488+k) (sourceBlock11488PiPairs.getD k (0,0))
    (sourceEtaBatch11488Lower k, sourceEtaBatch11488Upper k)
    (sourceBlock11488TwoPairs.getD k (0,0))

theorem sourceBlock11488Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11488XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11488+k):ℂ)).re ∧
      (xi (xiGridArgument (11488+k):ℂ)).re ≤ ((sourceBlock11488XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11488+k) _ _ _
    (sourceBlock11488PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11488_actual_enclosure k hk)
    (sourceBlock11488TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11488Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11488XiPair k).1 := by
  decide +kernel

theorem sourceBlock11488Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11488Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11488XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11488XiPair k)).2 ≤
      sourceBlock11488Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11488_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11488+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11488+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11488Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11488+k) (sourceBlock11488XiPair k) _
    (sourceBlock11488Xi_enclosure k hk) (sourceBlock11488Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11488Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11520_bound (k : ℕ) (hk : k < 11520) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11488
  · exact sourceRoundedMidpoint_first11488_bound k h
  · have hsum : 11488+(k-11488) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11488_bound (k-11488) (by omega)

end ReciprocalXi
