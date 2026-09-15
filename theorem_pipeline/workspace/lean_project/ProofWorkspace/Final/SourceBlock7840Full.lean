import ProofWorkspace.Final.SourceBlock7808Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7840DataFull
import ProofWorkspace.Final.EtaBlock7840Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7840XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7840+k) (sourceBlock7840PiPairs.getD k (0,0))
    (sourceEtaBatch7840Lower k, sourceEtaBatch7840Upper k)
    (sourceBlock7840TwoPairs.getD k (0,0))

theorem sourceBlock7840Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7840XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7840+k):ℂ)).re ∧
      (xi (xiGridArgument (7840+k):ℂ)).re ≤ ((sourceBlock7840XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7840+k) _ _ _
    (sourceBlock7840PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7840_actual_enclosure k hk)
    (sourceBlock7840TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7840Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7840XiPair k).1 := by
  decide +kernel

theorem sourceBlock7840Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7840Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7840XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7840XiPair k)).2 ≤
      sourceBlock7840Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7840_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7840+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7840+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7840Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7840+k) (sourceBlock7840XiPair k) _
    (sourceBlock7840Xi_enclosure k hk) (sourceBlock7840Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7840Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7872_bound (k : ℕ) (hk : k < 7872) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7840
  · exact sourceRoundedMidpoint_first7840_bound k h
  · have hsum : 7840+(k-7840) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7840_bound (k-7840) (by omega)

end ReciprocalXi
