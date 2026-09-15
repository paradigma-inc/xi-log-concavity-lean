import ProofWorkspace.Final.SourceBlock9856Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9888DataFull
import ProofWorkspace.Final.EtaBlock9888Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9888XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9888+k) (sourceBlock9888PiPairs.getD k (0,0))
    (sourceEtaBatch9888Lower k, sourceEtaBatch9888Upper k)
    (sourceBlock9888TwoPairs.getD k (0,0))

theorem sourceBlock9888Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9888XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9888+k):ℂ)).re ∧
      (xi (xiGridArgument (9888+k):ℂ)).re ≤ ((sourceBlock9888XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9888+k) _ _ _
    (sourceBlock9888PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9888_actual_enclosure k hk)
    (sourceBlock9888TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9888Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9888XiPair k).1 := by
  decide +kernel

theorem sourceBlock9888Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9888Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9888XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9888XiPair k)).2 ≤
      sourceBlock9888Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9888_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9888+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9888+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9888Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9888+k) (sourceBlock9888XiPair k) _
    (sourceBlock9888Xi_enclosure k hk) (sourceBlock9888Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9888Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9920_bound (k : ℕ) (hk : k < 9920) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9888
  · exact sourceRoundedMidpoint_first9888_bound k h
  · have hsum : 9888+(k-9888) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9888_bound (k-9888) (by omega)

end ReciprocalXi
