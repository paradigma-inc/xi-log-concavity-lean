import ProofWorkspace.Final.SourceBlock1216Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1248DataFull
import ProofWorkspace.Final.EtaBlock1248Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1248XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1248+k) (sourceBlock1248PiPairs.getD k (0,0))
    (sourceEtaBatch1248Lower k, sourceEtaBatch1248Upper k)
    (sourceBlock1248TwoPairs.getD k (0,0))

theorem sourceBlock1248Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1248XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1248+k):ℂ)).re ∧
      (xi (xiGridArgument (1248+k):ℂ)).re ≤ ((sourceBlock1248XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1248+k) _ _ _
    (sourceBlock1248PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1248_actual_enclosure k hk)
    (sourceBlock1248TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1248Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1248XiPair k).1 := by
  decide +kernel

theorem sourceBlock1248Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1248Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1248XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1248XiPair k)).2 ≤
      sourceBlock1248Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1248_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1248+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1248+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1248Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1248+k) (sourceBlock1248XiPair k) _
    (sourceBlock1248Xi_enclosure k hk) (sourceBlock1248Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1248Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first1280_bound (k : ℕ) (hk : k < 1280) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1248
  · exact sourceRoundedMidpoint_first1248_bound k h
  · have hsum : 1248+(k-1248) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1248_bound (k-1248) (by omega)

end ReciprocalXi
