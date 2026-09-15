import ProofWorkspace.Final.SourceBlock11136Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11168DataFull
import ProofWorkspace.Final.EtaBlock11168Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11168XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11168+k) (sourceBlock11168PiPairs.getD k (0,0))
    (sourceEtaBatch11168Lower k, sourceEtaBatch11168Upper k)
    (sourceBlock11168TwoPairs.getD k (0,0))

theorem sourceBlock11168Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11168XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11168+k):ℂ)).re ∧
      (xi (xiGridArgument (11168+k):ℂ)).re ≤ ((sourceBlock11168XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11168+k) _ _ _
    (sourceBlock11168PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11168_actual_enclosure k hk)
    (sourceBlock11168TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11168Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11168XiPair k).1 := by
  decide +kernel

theorem sourceBlock11168Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11168Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11168XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11168XiPair k)).2 ≤
      sourceBlock11168Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11168_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11168+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11168+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11168Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11168+k) (sourceBlock11168XiPair k) _
    (sourceBlock11168Xi_enclosure k hk) (sourceBlock11168Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11168Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11200_bound (k : ℕ) (hk : k < 11200) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11168
  · exact sourceRoundedMidpoint_first11168_bound k h
  · have hsum : 11168+(k-11168) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11168_bound (k-11168) (by omega)

end ReciprocalXi
