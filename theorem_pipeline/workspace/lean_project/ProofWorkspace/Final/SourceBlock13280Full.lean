import ProofWorkspace.Final.SourceBlock13248Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13280DataFull
import ProofWorkspace.Final.EtaBlock13280Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13280XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13280+k) (sourceBlock13280PiPairs.getD k (0,0))
    (sourceEtaBatch13280Lower k, sourceEtaBatch13280Upper k)
    (sourceBlock13280TwoPairs.getD k (0,0))

theorem sourceBlock13280Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13280XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13280+k):ℂ)).re ∧
      (xi (xiGridArgument (13280+k):ℂ)).re ≤ ((sourceBlock13280XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13280+k) _ _ _
    (sourceBlock13280PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13280_actual_enclosure k hk)
    (sourceBlock13280TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13280Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13280XiPair k).1 := by
  decide +kernel

theorem sourceBlock13280Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13280Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13280XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13280XiPair k)).2 ≤
      sourceBlock13280Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13280_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13280+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13280+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13280Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13280+k) (sourceBlock13280XiPair k) _
    (sourceBlock13280Xi_enclosure k hk) (sourceBlock13280Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13280Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13312_bound (k : ℕ) (hk : k < 13312) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13280
  · exact sourceRoundedMidpoint_first13280_bound k h
  · have hsum : 13280+(k-13280) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13280_bound (k-13280) (by omega)

end ReciprocalXi
