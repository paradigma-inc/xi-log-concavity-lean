import ProofWorkspace.Final.SourceBlock11072Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11104DataFull
import ProofWorkspace.Final.EtaBlock11104Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11104XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11104+k) (sourceBlock11104PiPairs.getD k (0,0))
    (sourceEtaBatch11104Lower k, sourceEtaBatch11104Upper k)
    (sourceBlock11104TwoPairs.getD k (0,0))

theorem sourceBlock11104Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11104XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11104+k):ℂ)).re ∧
      (xi (xiGridArgument (11104+k):ℂ)).re ≤ ((sourceBlock11104XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11104+k) _ _ _
    (sourceBlock11104PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11104_actual_enclosure k hk)
    (sourceBlock11104TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11104Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11104XiPair k).1 := by
  decide +kernel

theorem sourceBlock11104Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11104Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11104XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11104XiPair k)).2 ≤
      sourceBlock11104Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11104_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11104+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11104+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11104Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11104+k) (sourceBlock11104XiPair k) _
    (sourceBlock11104Xi_enclosure k hk) (sourceBlock11104Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11104Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11136_bound (k : ℕ) (hk : k < 11136) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11104
  · exact sourceRoundedMidpoint_first11104_bound k h
  · have hsum : 11104+(k-11104) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11104_bound (k-11104) (by omega)

end ReciprocalXi
