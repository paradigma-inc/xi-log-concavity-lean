import ProofWorkspace.Final.SourceBlock3264Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3296DataFull
import ProofWorkspace.Final.EtaBlock3296Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3296XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3296+k) (sourceBlock3296PiPairs.getD k (0,0))
    (sourceEtaBatch3296Lower k, sourceEtaBatch3296Upper k)
    (sourceBlock3296TwoPairs.getD k (0,0))

theorem sourceBlock3296Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3296XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3296+k):ℂ)).re ∧
      (xi (xiGridArgument (3296+k):ℂ)).re ≤ ((sourceBlock3296XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3296+k) _ _ _
    (sourceBlock3296PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3296_actual_enclosure k hk)
    (sourceBlock3296TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3296Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3296XiPair k).1 := by
  decide +kernel

theorem sourceBlock3296Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3296Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3296XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3296XiPair k)).2 ≤
      sourceBlock3296Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3296_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3296+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3296+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3296Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3296+k) (sourceBlock3296XiPair k) _
    (sourceBlock3296Xi_enclosure k hk) (sourceBlock3296Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3296Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3328_bound (k : ℕ) (hk : k < 3328) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3296
  · exact sourceRoundedMidpoint_first3296_bound k h
  · have hsum : 3296+(k-3296) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3296_bound (k-3296) (by omega)

end ReciprocalXi
