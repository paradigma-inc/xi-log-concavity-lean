import ProofWorkspace.Final.SourceBlock10176Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10208DataFull
import ProofWorkspace.Final.EtaBlock10208Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10208XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10208+k) (sourceBlock10208PiPairs.getD k (0,0))
    (sourceEtaBatch10208Lower k, sourceEtaBatch10208Upper k)
    (sourceBlock10208TwoPairs.getD k (0,0))

theorem sourceBlock10208Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10208XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10208+k):ℂ)).re ∧
      (xi (xiGridArgument (10208+k):ℂ)).re ≤ ((sourceBlock10208XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10208+k) _ _ _
    (sourceBlock10208PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10208_actual_enclosure k hk)
    (sourceBlock10208TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10208Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10208XiPair k).1 := by
  decide +kernel

theorem sourceBlock10208Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10208Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10208XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10208XiPair k)).2 ≤
      sourceBlock10208Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10208_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10208+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10208+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10208Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10208+k) (sourceBlock10208XiPair k) _
    (sourceBlock10208Xi_enclosure k hk) (sourceBlock10208Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10208Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10240_bound (k : ℕ) (hk : k < 10240) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10208
  · exact sourceRoundedMidpoint_first10208_bound k h
  · have hsum : 10208+(k-10208) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10208_bound (k-10208) (by omega)

end ReciprocalXi
