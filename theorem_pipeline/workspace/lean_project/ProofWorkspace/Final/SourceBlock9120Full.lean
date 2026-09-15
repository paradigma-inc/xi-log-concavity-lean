import ProofWorkspace.Final.SourceBlock9088Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9120DataFull
import ProofWorkspace.Final.EtaBlock9120Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9120XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9120+k) (sourceBlock9120PiPairs.getD k (0,0))
    (sourceEtaBatch9120Lower k, sourceEtaBatch9120Upper k)
    (sourceBlock9120TwoPairs.getD k (0,0))

theorem sourceBlock9120Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9120XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9120+k):ℂ)).re ∧
      (xi (xiGridArgument (9120+k):ℂ)).re ≤ ((sourceBlock9120XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9120+k) _ _ _
    (sourceBlock9120PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9120_actual_enclosure k hk)
    (sourceBlock9120TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9120Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9120XiPair k).1 := by
  decide +kernel

theorem sourceBlock9120Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9120Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9120XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9120XiPair k)).2 ≤
      sourceBlock9120Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9120_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9120+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9120+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9120Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9120+k) (sourceBlock9120XiPair k) _
    (sourceBlock9120Xi_enclosure k hk) (sourceBlock9120Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9120Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9152_bound (k : ℕ) (hk : k < 9152) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9120
  · exact sourceRoundedMidpoint_first9120_bound k h
  · have hsum : 9120+(k-9120) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9120_bound (k-9120) (by omega)

end ReciprocalXi
