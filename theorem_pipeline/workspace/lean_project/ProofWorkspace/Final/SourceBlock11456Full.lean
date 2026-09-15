import ProofWorkspace.Final.SourceBlock11424Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11456DataFull
import ProofWorkspace.Final.EtaBlock11456Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11456XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11456+k) (sourceBlock11456PiPairs.getD k (0,0))
    (sourceEtaBatch11456Lower k, sourceEtaBatch11456Upper k)
    (sourceBlock11456TwoPairs.getD k (0,0))

theorem sourceBlock11456Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11456XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11456+k):ℂ)).re ∧
      (xi (xiGridArgument (11456+k):ℂ)).re ≤ ((sourceBlock11456XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11456+k) _ _ _
    (sourceBlock11456PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11456_actual_enclosure k hk)
    (sourceBlock11456TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11456Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11456XiPair k).1 := by
  decide +kernel

theorem sourceBlock11456Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11456Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11456XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11456XiPair k)).2 ≤
      sourceBlock11456Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11456_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11456+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11456+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11456Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11456+k) (sourceBlock11456XiPair k) _
    (sourceBlock11456Xi_enclosure k hk) (sourceBlock11456Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11456Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11488_bound (k : ℕ) (hk : k < 11488) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11456
  · exact sourceRoundedMidpoint_first11456_bound k h
  · have hsum : 11456+(k-11456) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11456_bound (k-11456) (by omega)

end ReciprocalXi
