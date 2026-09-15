import ProofWorkspace.Final.SourceBlock9216Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9248DataFull
import ProofWorkspace.Final.EtaBlock9248Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9248XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9248+k) (sourceBlock9248PiPairs.getD k (0,0))
    (sourceEtaBatch9248Lower k, sourceEtaBatch9248Upper k)
    (sourceBlock9248TwoPairs.getD k (0,0))

theorem sourceBlock9248Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9248XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9248+k):ℂ)).re ∧
      (xi (xiGridArgument (9248+k):ℂ)).re ≤ ((sourceBlock9248XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9248+k) _ _ _
    (sourceBlock9248PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9248_actual_enclosure k hk)
    (sourceBlock9248TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9248Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9248XiPair k).1 := by
  decide +kernel

theorem sourceBlock9248Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9248Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9248XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9248XiPair k)).2 ≤
      sourceBlock9248Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9248_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9248+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9248+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9248Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9248+k) (sourceBlock9248XiPair k) _
    (sourceBlock9248Xi_enclosure k hk) (sourceBlock9248Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9248Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9280_bound (k : ℕ) (hk : k < 9280) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9248
  · exact sourceRoundedMidpoint_first9248_bound k h
  · have hsum : 9248+(k-9248) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9248_bound (k-9248) (by omega)

end ReciprocalXi
