import ProofWorkspace.Final.SourceBlock4608Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4640DataFull
import ProofWorkspace.Final.EtaBlock4640Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4640XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4640+k) (sourceBlock4640PiPairs.getD k (0,0))
    (sourceEtaBatch4640Lower k, sourceEtaBatch4640Upper k)
    (sourceBlock4640TwoPairs.getD k (0,0))

theorem sourceBlock4640Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4640XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4640+k):ℂ)).re ∧
      (xi (xiGridArgument (4640+k):ℂ)).re ≤ ((sourceBlock4640XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4640+k) _ _ _
    (sourceBlock4640PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4640_actual_enclosure k hk)
    (sourceBlock4640TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4640Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4640XiPair k).1 := by
  decide +kernel

theorem sourceBlock4640Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4640Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4640XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4640XiPair k)).2 ≤
      sourceBlock4640Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4640_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4640+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4640+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4640Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4640+k) (sourceBlock4640XiPair k) _
    (sourceBlock4640Xi_enclosure k hk) (sourceBlock4640Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4640Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4672_bound (k : ℕ) (hk : k < 4672) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4640
  · exact sourceRoundedMidpoint_first4640_bound k h
  · have hsum : 4640+(k-4640) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4640_bound (k-4640) (by omega)

end ReciprocalXi
