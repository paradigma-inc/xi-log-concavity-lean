import ProofWorkspace.Final.SourceBlock7616Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7648DataFull
import ProofWorkspace.Final.EtaBlock7648Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7648XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7648+k) (sourceBlock7648PiPairs.getD k (0,0))
    (sourceEtaBatch7648Lower k, sourceEtaBatch7648Upper k)
    (sourceBlock7648TwoPairs.getD k (0,0))

theorem sourceBlock7648Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7648XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7648+k):ℂ)).re ∧
      (xi (xiGridArgument (7648+k):ℂ)).re ≤ ((sourceBlock7648XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7648+k) _ _ _
    (sourceBlock7648PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7648_actual_enclosure k hk)
    (sourceBlock7648TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7648Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7648XiPair k).1 := by
  decide +kernel

theorem sourceBlock7648Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7648Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7648XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7648XiPair k)).2 ≤
      sourceBlock7648Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7648_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7648+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7648+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7648Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7648+k) (sourceBlock7648XiPair k) _
    (sourceBlock7648Xi_enclosure k hk) (sourceBlock7648Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7648Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7680_bound (k : ℕ) (hk : k < 7680) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7648
  · exact sourceRoundedMidpoint_first7648_bound k h
  · have hsum : 7648+(k-7648) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7648_bound (k-7648) (by omega)

end ReciprocalXi
