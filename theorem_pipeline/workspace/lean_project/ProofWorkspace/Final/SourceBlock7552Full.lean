import ProofWorkspace.Final.SourceBlock7520Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7552DataFull
import ProofWorkspace.Final.EtaBlock7552Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7552XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7552+k) (sourceBlock7552PiPairs.getD k (0,0))
    (sourceEtaBatch7552Lower k, sourceEtaBatch7552Upper k)
    (sourceBlock7552TwoPairs.getD k (0,0))

theorem sourceBlock7552Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7552XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7552+k):ℂ)).re ∧
      (xi (xiGridArgument (7552+k):ℂ)).re ≤ ((sourceBlock7552XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7552+k) _ _ _
    (sourceBlock7552PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7552_actual_enclosure k hk)
    (sourceBlock7552TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7552Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7552XiPair k).1 := by
  decide +kernel

theorem sourceBlock7552Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7552Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7552XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7552XiPair k)).2 ≤
      sourceBlock7552Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7552_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7552+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7552+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7552Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7552+k) (sourceBlock7552XiPair k) _
    (sourceBlock7552Xi_enclosure k hk) (sourceBlock7552Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7552Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7584_bound (k : ℕ) (hk : k < 7584) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7552
  · exact sourceRoundedMidpoint_first7552_bound k h
  · have hsum : 7552+(k-7552) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7552_bound (k-7552) (by omega)

end ReciprocalXi
