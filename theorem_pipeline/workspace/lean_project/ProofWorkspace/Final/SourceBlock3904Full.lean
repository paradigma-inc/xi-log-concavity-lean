import ProofWorkspace.Final.SourceBlock3872Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3904DataFull
import ProofWorkspace.Final.EtaBlock3904Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3904XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3904+k) (sourceBlock3904PiPairs.getD k (0,0))
    (sourceEtaBatch3904Lower k, sourceEtaBatch3904Upper k)
    (sourceBlock3904TwoPairs.getD k (0,0))

theorem sourceBlock3904Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3904XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3904+k):ℂ)).re ∧
      (xi (xiGridArgument (3904+k):ℂ)).re ≤ ((sourceBlock3904XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3904+k) _ _ _
    (sourceBlock3904PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3904_actual_enclosure k hk)
    (sourceBlock3904TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3904Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3904XiPair k).1 := by
  decide +kernel

theorem sourceBlock3904Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3904Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3904XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3904XiPair k)).2 ≤
      sourceBlock3904Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3904_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3904+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3904+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3904Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3904+k) (sourceBlock3904XiPair k) _
    (sourceBlock3904Xi_enclosure k hk) (sourceBlock3904Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3904Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3936_bound (k : ℕ) (hk : k < 3936) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3904
  · exact sourceRoundedMidpoint_first3904_bound k h
  · have hsum : 3904+(k-3904) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3904_bound (k-3904) (by omega)

end ReciprocalXi
