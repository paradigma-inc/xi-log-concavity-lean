import ProofWorkspace.Final.SourceBlock13152Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13184DataFull
import ProofWorkspace.Final.EtaBlock13184Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13184XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13184+k) (sourceBlock13184PiPairs.getD k (0,0))
    (sourceEtaBatch13184Lower k, sourceEtaBatch13184Upper k)
    (sourceBlock13184TwoPairs.getD k (0,0))

theorem sourceBlock13184Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13184XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13184+k):ℂ)).re ∧
      (xi (xiGridArgument (13184+k):ℂ)).re ≤ ((sourceBlock13184XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13184+k) _ _ _
    (sourceBlock13184PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13184_actual_enclosure k hk)
    (sourceBlock13184TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13184Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13184XiPair k).1 := by
  decide +kernel

theorem sourceBlock13184Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13184Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13184XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13184XiPair k)).2 ≤
      sourceBlock13184Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13184_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13184+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13184+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13184Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13184+k) (sourceBlock13184XiPair k) _
    (sourceBlock13184Xi_enclosure k hk) (sourceBlock13184Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13184Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13216_bound (k : ℕ) (hk : k < 13216) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13184
  · exact sourceRoundedMidpoint_first13184_bound k h
  · have hsum : 13184+(k-13184) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13184_bound (k-13184) (by omega)

end ReciprocalXi
