import ProofWorkspace.Final.SourceBlock4800Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4832DataFull
import ProofWorkspace.Final.EtaBlock4832Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4832XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4832+k) (sourceBlock4832PiPairs.getD k (0,0))
    (sourceEtaBatch4832Lower k, sourceEtaBatch4832Upper k)
    (sourceBlock4832TwoPairs.getD k (0,0))

theorem sourceBlock4832Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4832XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4832+k):ℂ)).re ∧
      (xi (xiGridArgument (4832+k):ℂ)).re ≤ ((sourceBlock4832XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4832+k) _ _ _
    (sourceBlock4832PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4832_actual_enclosure k hk)
    (sourceBlock4832TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4832Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4832XiPair k).1 := by
  decide +kernel

theorem sourceBlock4832Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4832Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4832XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4832XiPair k)).2 ≤
      sourceBlock4832Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4832_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4832+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4832+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4832Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4832+k) (sourceBlock4832XiPair k) _
    (sourceBlock4832Xi_enclosure k hk) (sourceBlock4832Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4832Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4864_bound (k : ℕ) (hk : k < 4864) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4832
  · exact sourceRoundedMidpoint_first4832_bound k h
  · have hsum : 4832+(k-4832) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4832_bound (k-4832) (by omega)

end ReciprocalXi
