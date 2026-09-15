import ProofWorkspace.Final.SourceBlock7168Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7200DataFull
import ProofWorkspace.Final.EtaBlock7200Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7200XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7200+k) (sourceBlock7200PiPairs.getD k (0,0))
    (sourceEtaBatch7200Lower k, sourceEtaBatch7200Upper k)
    (sourceBlock7200TwoPairs.getD k (0,0))

theorem sourceBlock7200Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7200XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7200+k):ℂ)).re ∧
      (xi (xiGridArgument (7200+k):ℂ)).re ≤ ((sourceBlock7200XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7200+k) _ _ _
    (sourceBlock7200PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7200_actual_enclosure k hk)
    (sourceBlock7200TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7200Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7200XiPair k).1 := by
  decide +kernel

theorem sourceBlock7200Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7200Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7200XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7200XiPair k)).2 ≤
      sourceBlock7200Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7200_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7200+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7200+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7200Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7200+k) (sourceBlock7200XiPair k) _
    (sourceBlock7200Xi_enclosure k hk) (sourceBlock7200Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7200Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7232_bound (k : ℕ) (hk : k < 7232) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7200
  · exact sourceRoundedMidpoint_first7200_bound k h
  · have hsum : 7200+(k-7200) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7200_bound (k-7200) (by omega)

end ReciprocalXi
