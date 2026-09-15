import ProofWorkspace.Final.SourceBlock3072Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3104DataFull
import ProofWorkspace.Final.EtaBlock3104Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3104XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3104+k) (sourceBlock3104PiPairs.getD k (0,0))
    (sourceEtaBatch3104Lower k, sourceEtaBatch3104Upper k)
    (sourceBlock3104TwoPairs.getD k (0,0))

theorem sourceBlock3104Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3104XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3104+k):ℂ)).re ∧
      (xi (xiGridArgument (3104+k):ℂ)).re ≤ ((sourceBlock3104XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3104+k) _ _ _
    (sourceBlock3104PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3104_actual_enclosure k hk)
    (sourceBlock3104TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3104Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3104XiPair k).1 := by
  decide +kernel

theorem sourceBlock3104Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3104Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3104XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3104XiPair k)).2 ≤
      sourceBlock3104Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3104_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3104+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3104+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3104Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3104+k) (sourceBlock3104XiPair k) _
    (sourceBlock3104Xi_enclosure k hk) (sourceBlock3104Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3104Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3136_bound (k : ℕ) (hk : k < 3136) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3104
  · exact sourceRoundedMidpoint_first3104_bound k h
  · have hsum : 3104+(k-3104) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3104_bound (k-3104) (by omega)

end ReciprocalXi
