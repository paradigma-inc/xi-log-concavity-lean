import ProofWorkspace.Final.SourceBlock11104Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11136DataFull
import ProofWorkspace.Final.EtaBlock11136Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11136XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11136+k) (sourceBlock11136PiPairs.getD k (0,0))
    (sourceEtaBatch11136Lower k, sourceEtaBatch11136Upper k)
    (sourceBlock11136TwoPairs.getD k (0,0))

theorem sourceBlock11136Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11136XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11136+k):ℂ)).re ∧
      (xi (xiGridArgument (11136+k):ℂ)).re ≤ ((sourceBlock11136XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11136+k) _ _ _
    (sourceBlock11136PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11136_actual_enclosure k hk)
    (sourceBlock11136TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11136Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11136XiPair k).1 := by
  decide +kernel

theorem sourceBlock11136Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11136Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11136XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11136XiPair k)).2 ≤
      sourceBlock11136Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11136_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11136+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11136+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11136Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11136+k) (sourceBlock11136XiPair k) _
    (sourceBlock11136Xi_enclosure k hk) (sourceBlock11136Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11136Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11168_bound (k : ℕ) (hk : k < 11168) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11136
  · exact sourceRoundedMidpoint_first11136_bound k h
  · have hsum : 11136+(k-11136) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11136_bound (k-11136) (by omega)

end ReciprocalXi
