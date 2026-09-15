import ProofWorkspace.Final.SourceBlock6304Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6336DataFull
import ProofWorkspace.Final.EtaBlock6336Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6336XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6336+k) (sourceBlock6336PiPairs.getD k (0,0))
    (sourceEtaBatch6336Lower k, sourceEtaBatch6336Upper k)
    (sourceBlock6336TwoPairs.getD k (0,0))

theorem sourceBlock6336Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6336XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6336+k):ℂ)).re ∧
      (xi (xiGridArgument (6336+k):ℂ)).re ≤ ((sourceBlock6336XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6336+k) _ _ _
    (sourceBlock6336PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6336_actual_enclosure k hk)
    (sourceBlock6336TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6336Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6336XiPair k).1 := by
  decide +kernel

theorem sourceBlock6336Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6336Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6336XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6336XiPair k)).2 ≤
      sourceBlock6336Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6336_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6336+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6336+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6336Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6336+k) (sourceBlock6336XiPair k) _
    (sourceBlock6336Xi_enclosure k hk) (sourceBlock6336Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6336Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6368_bound (k : ℕ) (hk : k < 6368) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6336
  · exact sourceRoundedMidpoint_first6336_bound k h
  · have hsum : 6336+(k-6336) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6336_bound (k-6336) (by omega)

end ReciprocalXi
