import ProofWorkspace.Final.SourceBlock5824Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5856DataFull
import ProofWorkspace.Final.EtaBlock5856Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5856XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5856+k) (sourceBlock5856PiPairs.getD k (0,0))
    (sourceEtaBatch5856Lower k, sourceEtaBatch5856Upper k)
    (sourceBlock5856TwoPairs.getD k (0,0))

theorem sourceBlock5856Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5856XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5856+k):ℂ)).re ∧
      (xi (xiGridArgument (5856+k):ℂ)).re ≤ ((sourceBlock5856XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5856+k) _ _ _
    (sourceBlock5856PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5856_actual_enclosure k hk)
    (sourceBlock5856TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5856Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5856XiPair k).1 := by
  decide +kernel

theorem sourceBlock5856Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5856Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5856XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5856XiPair k)).2 ≤
      sourceBlock5856Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5856_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5856+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5856+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5856Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5856+k) (sourceBlock5856XiPair k) _
    (sourceBlock5856Xi_enclosure k hk) (sourceBlock5856Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5856Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5888_bound (k : ℕ) (hk : k < 5888) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5856
  · exact sourceRoundedMidpoint_first5856_bound k h
  · have hsum : 5856+(k-5856) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5856_bound (k-5856) (by omega)

end ReciprocalXi
