import ProofWorkspace.Final.SourceBlock10272Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10304DataFull
import ProofWorkspace.Final.EtaBlock10304Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10304XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10304+k) (sourceBlock10304PiPairs.getD k (0,0))
    (sourceEtaBatch10304Lower k, sourceEtaBatch10304Upper k)
    (sourceBlock10304TwoPairs.getD k (0,0))

theorem sourceBlock10304Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10304XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10304+k):ℂ)).re ∧
      (xi (xiGridArgument (10304+k):ℂ)).re ≤ ((sourceBlock10304XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10304+k) _ _ _
    (sourceBlock10304PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10304_actual_enclosure k hk)
    (sourceBlock10304TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10304Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10304XiPair k).1 := by
  decide +kernel

theorem sourceBlock10304Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10304Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10304XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10304XiPair k)).2 ≤
      sourceBlock10304Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10304_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10304+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10304+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10304Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10304+k) (sourceBlock10304XiPair k) _
    (sourceBlock10304Xi_enclosure k hk) (sourceBlock10304Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10304Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10336_bound (k : ℕ) (hk : k < 10336) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10304
  · exact sourceRoundedMidpoint_first10304_bound k h
  · have hsum : 10304+(k-10304) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10304_bound (k-10304) (by omega)

end ReciprocalXi
