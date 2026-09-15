import ProofWorkspace.Final.SourceBlock7840Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7872DataFull
import ProofWorkspace.Final.EtaBlock7872Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7872XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7872+k) (sourceBlock7872PiPairs.getD k (0,0))
    (sourceEtaBatch7872Lower k, sourceEtaBatch7872Upper k)
    (sourceBlock7872TwoPairs.getD k (0,0))

theorem sourceBlock7872Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7872XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7872+k):ℂ)).re ∧
      (xi (xiGridArgument (7872+k):ℂ)).re ≤ ((sourceBlock7872XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7872+k) _ _ _
    (sourceBlock7872PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7872_actual_enclosure k hk)
    (sourceBlock7872TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7872Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7872XiPair k).1 := by
  decide +kernel

theorem sourceBlock7872Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7872Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7872XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7872XiPair k)).2 ≤
      sourceBlock7872Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7872_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7872+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7872+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7872Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7872+k) (sourceBlock7872XiPair k) _
    (sourceBlock7872Xi_enclosure k hk) (sourceBlock7872Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7872Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7904_bound (k : ℕ) (hk : k < 7904) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7872
  · exact sourceRoundedMidpoint_first7872_bound k h
  · have hsum : 7872+(k-7872) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7872_bound (k-7872) (by omega)

end ReciprocalXi
