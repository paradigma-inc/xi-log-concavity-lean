import ProofWorkspace.Final.SourceBlock9472Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9504DataFull
import ProofWorkspace.Final.EtaBlock9504Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9504XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9504+k) (sourceBlock9504PiPairs.getD k (0,0))
    (sourceEtaBatch9504Lower k, sourceEtaBatch9504Upper k)
    (sourceBlock9504TwoPairs.getD k (0,0))

theorem sourceBlock9504Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9504XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9504+k):ℂ)).re ∧
      (xi (xiGridArgument (9504+k):ℂ)).re ≤ ((sourceBlock9504XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9504+k) _ _ _
    (sourceBlock9504PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9504_actual_enclosure k hk)
    (sourceBlock9504TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9504Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9504XiPair k).1 := by
  decide +kernel

theorem sourceBlock9504Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9504Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9504XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9504XiPair k)).2 ≤
      sourceBlock9504Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9504_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9504+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9504+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9504Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9504+k) (sourceBlock9504XiPair k) _
    (sourceBlock9504Xi_enclosure k hk) (sourceBlock9504Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9504Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9536_bound (k : ℕ) (hk : k < 9536) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9504
  · exact sourceRoundedMidpoint_first9504_bound k h
  · have hsum : 9504+(k-9504) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9504_bound (k-9504) (by omega)

end ReciprocalXi
