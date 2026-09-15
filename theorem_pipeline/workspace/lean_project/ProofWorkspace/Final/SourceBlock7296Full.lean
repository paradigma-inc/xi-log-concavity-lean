import ProofWorkspace.Final.SourceBlock7264Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7296DataFull
import ProofWorkspace.Final.EtaBlock7296Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7296XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7296+k) (sourceBlock7296PiPairs.getD k (0,0))
    (sourceEtaBatch7296Lower k, sourceEtaBatch7296Upper k)
    (sourceBlock7296TwoPairs.getD k (0,0))

theorem sourceBlock7296Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7296XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7296+k):ℂ)).re ∧
      (xi (xiGridArgument (7296+k):ℂ)).re ≤ ((sourceBlock7296XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7296+k) _ _ _
    (sourceBlock7296PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7296_actual_enclosure k hk)
    (sourceBlock7296TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7296Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7296XiPair k).1 := by
  decide +kernel

theorem sourceBlock7296Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7296Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7296XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7296XiPair k)).2 ≤
      sourceBlock7296Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7296_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7296+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7296+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7296Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7296+k) (sourceBlock7296XiPair k) _
    (sourceBlock7296Xi_enclosure k hk) (sourceBlock7296Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7296Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7328_bound (k : ℕ) (hk : k < 7328) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7296
  · exact sourceRoundedMidpoint_first7296_bound k h
  · have hsum : 7296+(k-7296) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7296_bound (k-7296) (by omega)

end ReciprocalXi
