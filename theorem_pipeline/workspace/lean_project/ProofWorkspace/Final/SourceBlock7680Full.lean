import ProofWorkspace.Final.SourceBlock7648Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7680DataFull
import ProofWorkspace.Final.EtaBlock7680Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7680XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7680+k) (sourceBlock7680PiPairs.getD k (0,0))
    (sourceEtaBatch7680Lower k, sourceEtaBatch7680Upper k)
    (sourceBlock7680TwoPairs.getD k (0,0))

theorem sourceBlock7680Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7680XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7680+k):ℂ)).re ∧
      (xi (xiGridArgument (7680+k):ℂ)).re ≤ ((sourceBlock7680XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7680+k) _ _ _
    (sourceBlock7680PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7680_actual_enclosure k hk)
    (sourceBlock7680TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7680Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7680XiPair k).1 := by
  decide +kernel

theorem sourceBlock7680Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7680Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7680XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7680XiPair k)).2 ≤
      sourceBlock7680Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7680_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7680+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7680+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7680Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7680+k) (sourceBlock7680XiPair k) _
    (sourceBlock7680Xi_enclosure k hk) (sourceBlock7680Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7680Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7712_bound (k : ℕ) (hk : k < 7712) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7680
  · exact sourceRoundedMidpoint_first7680_bound k h
  · have hsum : 7680+(k-7680) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7680_bound (k-7680) (by omega)

end ReciprocalXi
