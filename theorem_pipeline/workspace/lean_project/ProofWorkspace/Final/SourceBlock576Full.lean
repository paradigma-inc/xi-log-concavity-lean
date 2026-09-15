import ProofWorkspace.Final.SourceBlock544Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock576DataFull
import ProofWorkspace.Final.EtaBlock576Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock576XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (576+k) (sourceBlock576PiPairs.getD k (0,0))
    (sourceEtaBatch576Lower k, sourceEtaBatch576Upper k)
    (sourceBlock576TwoPairs.getD k (0,0))

theorem sourceBlock576Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock576XiPair k).1:ℝ) ≤ (xi (xiGridArgument (576+k):ℂ)).re ∧
      (xi (xiGridArgument (576+k):ℂ)).re ≤ ((sourceBlock576XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (576+k) _ _ _
    (sourceBlock576PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch576_actual_enclosure k hk)
    (sourceBlock576TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock576Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock576XiPair k).1 := by
  decide +kernel

theorem sourceBlock576Reciprocal_check : ∀ k : Fin 32,
    sourceBlock576Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock576XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock576XiPair k)).2 ≤
      sourceBlock576Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block576_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((576+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (576+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock576Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (576+k) (sourceBlock576XiPair k) _
    (sourceBlock576Xi_enclosure k hk) (sourceBlock576Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock576Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first608_bound (k : ℕ) (hk : k < 608) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 576
  · exact sourceRoundedMidpoint_first576_bound k h
  · have hsum : 576+(k-576) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block576_bound (k-576) (by omega)

end ReciprocalXi
