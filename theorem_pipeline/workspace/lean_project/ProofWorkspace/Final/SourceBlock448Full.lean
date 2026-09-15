import ProofWorkspace.Final.SourceBlock416Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock448DataFull
import ProofWorkspace.Final.EtaBlock448Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock448XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (448+k) (sourceBlock448PiPairs.getD k (0,0))
    (sourceEtaBatch448Lower k, sourceEtaBatch448Upper k)
    (sourceBlock448TwoPairs.getD k (0,0))

theorem sourceBlock448Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock448XiPair k).1:ℝ) ≤ (xi (xiGridArgument (448+k):ℂ)).re ∧
      (xi (xiGridArgument (448+k):ℂ)).re ≤ ((sourceBlock448XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (448+k) _ _ _
    (sourceBlock448PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch448_actual_enclosure k hk)
    (sourceBlock448TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock448Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock448XiPair k).1 := by
  decide +kernel

theorem sourceBlock448Reciprocal_check : ∀ k : Fin 32,
    sourceBlock448Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock448XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock448XiPair k)).2 ≤
      sourceBlock448Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block448_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((448+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (448+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock448Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (448+k) (sourceBlock448XiPair k) _
    (sourceBlock448Xi_enclosure k hk) (sourceBlock448Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock448Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first480_bound (k : ℕ) (hk : k < 480) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 448
  · exact sourceRoundedMidpoint_first448_bound k h
  · have hsum : 448+(k-448) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block448_bound (k-448) (by omega)

end ReciprocalXi
