import ProofWorkspace.Final.SourceBlock5152Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5184DataFull
import ProofWorkspace.Final.EtaBlock5184Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5184XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5184+k) (sourceBlock5184PiPairs.getD k (0,0))
    (sourceEtaBatch5184Lower k, sourceEtaBatch5184Upper k)
    (sourceBlock5184TwoPairs.getD k (0,0))

theorem sourceBlock5184Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5184XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5184+k):ℂ)).re ∧
      (xi (xiGridArgument (5184+k):ℂ)).re ≤ ((sourceBlock5184XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5184+k) _ _ _
    (sourceBlock5184PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5184_actual_enclosure k hk)
    (sourceBlock5184TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5184Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5184XiPair k).1 := by
  decide +kernel

theorem sourceBlock5184Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5184Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5184XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5184XiPair k)).2 ≤
      sourceBlock5184Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5184_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5184+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5184+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5184Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5184+k) (sourceBlock5184XiPair k) _
    (sourceBlock5184Xi_enclosure k hk) (sourceBlock5184Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5184Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5216_bound (k : ℕ) (hk : k < 5216) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5184
  · exact sourceRoundedMidpoint_first5184_bound k h
  · have hsum : 5184+(k-5184) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5184_bound (k-5184) (by omega)

end ReciprocalXi
