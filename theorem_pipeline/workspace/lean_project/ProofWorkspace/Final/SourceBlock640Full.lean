import ProofWorkspace.Final.SourceBlock608Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock640DataFull
import ProofWorkspace.Final.EtaBlock640Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock640XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (640+k) (sourceBlock640PiPairs.getD k (0,0))
    (sourceEtaBatch640Lower k, sourceEtaBatch640Upper k)
    (sourceBlock640TwoPairs.getD k (0,0))

theorem sourceBlock640Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock640XiPair k).1:ℝ) ≤ (xi (xiGridArgument (640+k):ℂ)).re ∧
      (xi (xiGridArgument (640+k):ℂ)).re ≤ ((sourceBlock640XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (640+k) _ _ _
    (sourceBlock640PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch640_actual_enclosure k hk)
    (sourceBlock640TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock640Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock640XiPair k).1 := by
  decide +kernel

theorem sourceBlock640Reciprocal_check : ∀ k : Fin 32,
    sourceBlock640Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock640XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock640XiPair k)).2 ≤
      sourceBlock640Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block640_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((640+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (640+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock640Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (640+k) (sourceBlock640XiPair k) _
    (sourceBlock640Xi_enclosure k hk) (sourceBlock640Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock640Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first672_bound (k : ℕ) (hk : k < 672) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 640
  · exact sourceRoundedMidpoint_first640_bound k h
  · have hsum : 640+(k-640) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block640_bound (k-640) (by omega)

end ReciprocalXi
