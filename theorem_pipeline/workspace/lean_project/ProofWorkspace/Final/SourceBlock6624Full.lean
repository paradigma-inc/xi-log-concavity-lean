import ProofWorkspace.Final.SourceBlock6592Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6624DataFull
import ProofWorkspace.Final.EtaBlock6624Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6624XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6624+k) (sourceBlock6624PiPairs.getD k (0,0))
    (sourceEtaBatch6624Lower k, sourceEtaBatch6624Upper k)
    (sourceBlock6624TwoPairs.getD k (0,0))

theorem sourceBlock6624Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6624XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6624+k):ℂ)).re ∧
      (xi (xiGridArgument (6624+k):ℂ)).re ≤ ((sourceBlock6624XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6624+k) _ _ _
    (sourceBlock6624PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6624_actual_enclosure k hk)
    (sourceBlock6624TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6624Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6624XiPair k).1 := by
  decide +kernel

theorem sourceBlock6624Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6624Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6624XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6624XiPair k)).2 ≤
      sourceBlock6624Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6624_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6624+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6624+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6624Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6624+k) (sourceBlock6624XiPair k) _
    (sourceBlock6624Xi_enclosure k hk) (sourceBlock6624Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6624Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6656_bound (k : ℕ) (hk : k < 6656) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6624
  · exact sourceRoundedMidpoint_first6624_bound k h
  · have hsum : 6624+(k-6624) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6624_bound (k-6624) (by omega)

end ReciprocalXi
