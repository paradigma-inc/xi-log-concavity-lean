import ProofWorkspace.Final.SourceBlock12992Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13024DataFull
import ProofWorkspace.Final.EtaBlock13024Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13024XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13024+k) (sourceBlock13024PiPairs.getD k (0,0))
    (sourceEtaBatch13024Lower k, sourceEtaBatch13024Upper k)
    (sourceBlock13024TwoPairs.getD k (0,0))

theorem sourceBlock13024Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13024XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13024+k):ℂ)).re ∧
      (xi (xiGridArgument (13024+k):ℂ)).re ≤ ((sourceBlock13024XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13024+k) _ _ _
    (sourceBlock13024PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13024_actual_enclosure k hk)
    (sourceBlock13024TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13024Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13024XiPair k).1 := by
  decide +kernel

theorem sourceBlock13024Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13024Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13024XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13024XiPair k)).2 ≤
      sourceBlock13024Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13024_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13024+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13024+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13024Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13024+k) (sourceBlock13024XiPair k) _
    (sourceBlock13024Xi_enclosure k hk) (sourceBlock13024Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13024Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13056_bound (k : ℕ) (hk : k < 13056) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13024
  · exact sourceRoundedMidpoint_first13024_bound k h
  · have hsum : 13024+(k-13024) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13024_bound (k-13024) (by omega)

end ReciprocalXi
