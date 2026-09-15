import ProofWorkspace.Final.SourceBlock7072Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7104DataFull
import ProofWorkspace.Final.EtaBlock7104Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7104XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7104+k) (sourceBlock7104PiPairs.getD k (0,0))
    (sourceEtaBatch7104Lower k, sourceEtaBatch7104Upper k)
    (sourceBlock7104TwoPairs.getD k (0,0))

theorem sourceBlock7104Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7104XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7104+k):ℂ)).re ∧
      (xi (xiGridArgument (7104+k):ℂ)).re ≤ ((sourceBlock7104XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7104+k) _ _ _
    (sourceBlock7104PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7104_actual_enclosure k hk)
    (sourceBlock7104TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7104Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7104XiPair k).1 := by
  decide +kernel

theorem sourceBlock7104Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7104Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7104XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7104XiPair k)).2 ≤
      sourceBlock7104Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7104_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7104+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7104+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7104Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7104+k) (sourceBlock7104XiPair k) _
    (sourceBlock7104Xi_enclosure k hk) (sourceBlock7104Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7104Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7136_bound (k : ℕ) (hk : k < 7136) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7104
  · exact sourceRoundedMidpoint_first7104_bound k h
  · have hsum : 7104+(k-7104) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7104_bound (k-7104) (by omega)

end ReciprocalXi
