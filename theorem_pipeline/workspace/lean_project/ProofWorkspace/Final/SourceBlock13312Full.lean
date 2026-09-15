import ProofWorkspace.Final.SourceBlock13280Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13312DataFull
import ProofWorkspace.Final.EtaBlock13312Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13312XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13312+k) (sourceBlock13312PiPairs.getD k (0,0))
    (sourceEtaBatch13312Lower k, sourceEtaBatch13312Upper k)
    (sourceBlock13312TwoPairs.getD k (0,0))

theorem sourceBlock13312Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13312XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13312+k):ℂ)).re ∧
      (xi (xiGridArgument (13312+k):ℂ)).re ≤ ((sourceBlock13312XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13312+k) _ _ _
    (sourceBlock13312PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13312_actual_enclosure k hk)
    (sourceBlock13312TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13312Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13312XiPair k).1 := by
  decide +kernel

theorem sourceBlock13312Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13312Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13312XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13312XiPair k)).2 ≤
      sourceBlock13312Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13312_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13312+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13312+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13312Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13312+k) (sourceBlock13312XiPair k) _
    (sourceBlock13312Xi_enclosure k hk) (sourceBlock13312Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13312Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13344_bound (k : ℕ) (hk : k < 13344) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13312
  · exact sourceRoundedMidpoint_first13312_bound k h
  · have hsum : 13312+(k-13312) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13312_bound (k-13312) (by omega)

end ReciprocalXi
