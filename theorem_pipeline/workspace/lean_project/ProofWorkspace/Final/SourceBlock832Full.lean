import ProofWorkspace.Final.SourceBlock800Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock832DataFull
import ProofWorkspace.Final.EtaBlock832Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock832XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (832+k) (sourceBlock832PiPairs.getD k (0,0))
    (sourceEtaBatch832Lower k, sourceEtaBatch832Upper k)
    (sourceBlock832TwoPairs.getD k (0,0))

theorem sourceBlock832Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock832XiPair k).1:ℝ) ≤ (xi (xiGridArgument (832+k):ℂ)).re ∧
      (xi (xiGridArgument (832+k):ℂ)).re ≤ ((sourceBlock832XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (832+k) _ _ _
    (sourceBlock832PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch832_actual_enclosure k hk)
    (sourceBlock832TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock832Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock832XiPair k).1 := by
  decide +kernel

theorem sourceBlock832Reciprocal_check : ∀ k : Fin 32,
    sourceBlock832Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock832XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock832XiPair k)).2 ≤
      sourceBlock832Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block832_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((832+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (832+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock832Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (832+k) (sourceBlock832XiPair k) _
    (sourceBlock832Xi_enclosure k hk) (sourceBlock832Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock832Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first864_bound (k : ℕ) (hk : k < 864) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 832
  · exact sourceRoundedMidpoint_first832_bound k h
  · have hsum : 832+(k-832) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block832_bound (k-832) (by omega)

end ReciprocalXi
