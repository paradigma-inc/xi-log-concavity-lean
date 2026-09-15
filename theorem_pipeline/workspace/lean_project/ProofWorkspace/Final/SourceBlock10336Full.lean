import ProofWorkspace.Final.SourceBlock10304Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10336DataFull
import ProofWorkspace.Final.EtaBlock10336Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10336XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10336+k) (sourceBlock10336PiPairs.getD k (0,0))
    (sourceEtaBatch10336Lower k, sourceEtaBatch10336Upper k)
    (sourceBlock10336TwoPairs.getD k (0,0))

theorem sourceBlock10336Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10336XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10336+k):ℂ)).re ∧
      (xi (xiGridArgument (10336+k):ℂ)).re ≤ ((sourceBlock10336XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10336+k) _ _ _
    (sourceBlock10336PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10336_actual_enclosure k hk)
    (sourceBlock10336TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10336Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10336XiPair k).1 := by
  decide +kernel

theorem sourceBlock10336Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10336Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10336XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10336XiPair k)).2 ≤
      sourceBlock10336Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10336_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10336+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10336+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10336Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10336+k) (sourceBlock10336XiPair k) _
    (sourceBlock10336Xi_enclosure k hk) (sourceBlock10336Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10336Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10368_bound (k : ℕ) (hk : k < 10368) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10336
  · exact sourceRoundedMidpoint_first10336_bound k h
  · have hsum : 10336+(k-10336) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10336_bound (k-10336) (by omega)

end ReciprocalXi
