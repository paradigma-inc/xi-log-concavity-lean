import ProofWorkspace.Final.SourceBlock9824Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9856DataFull
import ProofWorkspace.Final.EtaBlock9856Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9856XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9856+k) (sourceBlock9856PiPairs.getD k (0,0))
    (sourceEtaBatch9856Lower k, sourceEtaBatch9856Upper k)
    (sourceBlock9856TwoPairs.getD k (0,0))

theorem sourceBlock9856Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9856XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9856+k):ℂ)).re ∧
      (xi (xiGridArgument (9856+k):ℂ)).re ≤ ((sourceBlock9856XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9856+k) _ _ _
    (sourceBlock9856PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9856_actual_enclosure k hk)
    (sourceBlock9856TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9856Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9856XiPair k).1 := by
  decide +kernel

theorem sourceBlock9856Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9856Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9856XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9856XiPair k)).2 ≤
      sourceBlock9856Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9856_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9856+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9856+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9856Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9856+k) (sourceBlock9856XiPair k) _
    (sourceBlock9856Xi_enclosure k hk) (sourceBlock9856Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9856Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9888_bound (k : ℕ) (hk : k < 9888) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9856
  · exact sourceRoundedMidpoint_first9856_bound k h
  · have hsum : 9856+(k-9856) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9856_bound (k-9856) (by omega)

end ReciprocalXi
