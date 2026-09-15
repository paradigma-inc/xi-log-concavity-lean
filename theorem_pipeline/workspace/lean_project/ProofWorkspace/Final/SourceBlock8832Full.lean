import ProofWorkspace.Final.SourceBlock8800Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8832DataFull
import ProofWorkspace.Final.EtaBlock8832Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8832XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8832+k) (sourceBlock8832PiPairs.getD k (0,0))
    (sourceEtaBatch8832Lower k, sourceEtaBatch8832Upper k)
    (sourceBlock8832TwoPairs.getD k (0,0))

theorem sourceBlock8832Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8832XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8832+k):ℂ)).re ∧
      (xi (xiGridArgument (8832+k):ℂ)).re ≤ ((sourceBlock8832XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8832+k) _ _ _
    (sourceBlock8832PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8832_actual_enclosure k hk)
    (sourceBlock8832TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8832Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8832XiPair k).1 := by
  decide +kernel

theorem sourceBlock8832Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8832Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8832XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8832XiPair k)).2 ≤
      sourceBlock8832Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8832_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8832+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8832+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8832Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8832+k) (sourceBlock8832XiPair k) _
    (sourceBlock8832Xi_enclosure k hk) (sourceBlock8832Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8832Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8864_bound (k : ℕ) (hk : k < 8864) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8832
  · exact sourceRoundedMidpoint_first8832_bound k h
  · have hsum : 8832+(k-8832) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8832_bound (k-8832) (by omega)

end ReciprocalXi
