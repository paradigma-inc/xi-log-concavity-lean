import ProofWorkspace.Final.SourceBlock7456Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7488DataFull
import ProofWorkspace.Final.EtaBlock7488Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7488XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7488+k) (sourceBlock7488PiPairs.getD k (0,0))
    (sourceEtaBatch7488Lower k, sourceEtaBatch7488Upper k)
    (sourceBlock7488TwoPairs.getD k (0,0))

theorem sourceBlock7488Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7488XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7488+k):ℂ)).re ∧
      (xi (xiGridArgument (7488+k):ℂ)).re ≤ ((sourceBlock7488XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7488+k) _ _ _
    (sourceBlock7488PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7488_actual_enclosure k hk)
    (sourceBlock7488TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7488Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7488XiPair k).1 := by
  decide +kernel

theorem sourceBlock7488Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7488Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7488XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7488XiPair k)).2 ≤
      sourceBlock7488Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7488_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7488+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7488+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7488Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7488+k) (sourceBlock7488XiPair k) _
    (sourceBlock7488Xi_enclosure k hk) (sourceBlock7488Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7488Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7520_bound (k : ℕ) (hk : k < 7520) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7488
  · exact sourceRoundedMidpoint_first7488_bound k h
  · have hsum : 7488+(k-7488) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7488_bound (k-7488) (by omega)

end ReciprocalXi
