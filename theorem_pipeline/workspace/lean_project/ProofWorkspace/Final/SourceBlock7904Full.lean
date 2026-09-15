import ProofWorkspace.Final.SourceBlock7872Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7904DataFull
import ProofWorkspace.Final.EtaBlock7904Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7904XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7904+k) (sourceBlock7904PiPairs.getD k (0,0))
    (sourceEtaBatch7904Lower k, sourceEtaBatch7904Upper k)
    (sourceBlock7904TwoPairs.getD k (0,0))

theorem sourceBlock7904Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7904XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7904+k):ℂ)).re ∧
      (xi (xiGridArgument (7904+k):ℂ)).re ≤ ((sourceBlock7904XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7904+k) _ _ _
    (sourceBlock7904PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7904_actual_enclosure k hk)
    (sourceBlock7904TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7904Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7904XiPair k).1 := by
  decide +kernel

theorem sourceBlock7904Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7904Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7904XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7904XiPair k)).2 ≤
      sourceBlock7904Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7904_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7904+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7904+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7904Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7904+k) (sourceBlock7904XiPair k) _
    (sourceBlock7904Xi_enclosure k hk) (sourceBlock7904Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7904Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7936_bound (k : ℕ) (hk : k < 7936) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7904
  · exact sourceRoundedMidpoint_first7904_bound k h
  · have hsum : 7904+(k-7904) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7904_bound (k-7904) (by omega)

end ReciprocalXi
