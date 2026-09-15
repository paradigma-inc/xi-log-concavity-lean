import ProofWorkspace.Final.SourceBlock10752Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10784DataFull
import ProofWorkspace.Final.EtaBlock10784Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10784XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10784+k) (sourceBlock10784PiPairs.getD k (0,0))
    (sourceEtaBatch10784Lower k, sourceEtaBatch10784Upper k)
    (sourceBlock10784TwoPairs.getD k (0,0))

theorem sourceBlock10784Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10784XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10784+k):ℂ)).re ∧
      (xi (xiGridArgument (10784+k):ℂ)).re ≤ ((sourceBlock10784XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10784+k) _ _ _
    (sourceBlock10784PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10784_actual_enclosure k hk)
    (sourceBlock10784TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10784Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10784XiPair k).1 := by
  decide +kernel

theorem sourceBlock10784Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10784Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10784XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10784XiPair k)).2 ≤
      sourceBlock10784Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10784_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10784+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10784+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10784Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10784+k) (sourceBlock10784XiPair k) _
    (sourceBlock10784Xi_enclosure k hk) (sourceBlock10784Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10784Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10816_bound (k : ℕ) (hk : k < 10816) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10784
  · exact sourceRoundedMidpoint_first10784_bound k h
  · have hsum : 10784+(k-10784) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10784_bound (k-10784) (by omega)

end ReciprocalXi
