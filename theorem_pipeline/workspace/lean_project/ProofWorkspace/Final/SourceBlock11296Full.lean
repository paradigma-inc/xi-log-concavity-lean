import ProofWorkspace.Final.SourceBlock11264Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11296DataFull
import ProofWorkspace.Final.EtaBlock11296Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11296XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11296+k) (sourceBlock11296PiPairs.getD k (0,0))
    (sourceEtaBatch11296Lower k, sourceEtaBatch11296Upper k)
    (sourceBlock11296TwoPairs.getD k (0,0))

theorem sourceBlock11296Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11296XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11296+k):ℂ)).re ∧
      (xi (xiGridArgument (11296+k):ℂ)).re ≤ ((sourceBlock11296XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11296+k) _ _ _
    (sourceBlock11296PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11296_actual_enclosure k hk)
    (sourceBlock11296TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11296Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11296XiPair k).1 := by
  decide +kernel

theorem sourceBlock11296Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11296Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11296XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11296XiPair k)).2 ≤
      sourceBlock11296Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11296_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11296+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11296+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11296Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11296+k) (sourceBlock11296XiPair k) _
    (sourceBlock11296Xi_enclosure k hk) (sourceBlock11296Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11296Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11328_bound (k : ℕ) (hk : k < 11328) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11296
  · exact sourceRoundedMidpoint_first11296_bound k h
  · have hsum : 11296+(k-11296) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11296_bound (k-11296) (by omega)

end ReciprocalXi
