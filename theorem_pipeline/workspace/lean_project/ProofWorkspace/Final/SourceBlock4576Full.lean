import ProofWorkspace.Final.SourceBlock4544Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4576DataFull
import ProofWorkspace.Final.EtaBlock4576Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4576XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4576+k) (sourceBlock4576PiPairs.getD k (0,0))
    (sourceEtaBatch4576Lower k, sourceEtaBatch4576Upper k)
    (sourceBlock4576TwoPairs.getD k (0,0))

theorem sourceBlock4576Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4576XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4576+k):ℂ)).re ∧
      (xi (xiGridArgument (4576+k):ℂ)).re ≤ ((sourceBlock4576XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4576+k) _ _ _
    (sourceBlock4576PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4576_actual_enclosure k hk)
    (sourceBlock4576TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4576Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4576XiPair k).1 := by
  decide +kernel

theorem sourceBlock4576Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4576Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4576XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4576XiPair k)).2 ≤
      sourceBlock4576Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4576_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4576+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4576+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4576Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4576+k) (sourceBlock4576XiPair k) _
    (sourceBlock4576Xi_enclosure k hk) (sourceBlock4576Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4576Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4608_bound (k : ℕ) (hk : k < 4608) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4576
  · exact sourceRoundedMidpoint_first4576_bound k h
  · have hsum : 4576+(k-4576) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4576_bound (k-4576) (by omega)

end ReciprocalXi
