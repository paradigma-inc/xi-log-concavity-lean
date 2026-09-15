import ProofWorkspace.Final.SourceBlock6816Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6848DataFull
import ProofWorkspace.Final.EtaBlock6848Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6848XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6848+k) (sourceBlock6848PiPairs.getD k (0,0))
    (sourceEtaBatch6848Lower k, sourceEtaBatch6848Upper k)
    (sourceBlock6848TwoPairs.getD k (0,0))

theorem sourceBlock6848Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6848XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6848+k):ℂ)).re ∧
      (xi (xiGridArgument (6848+k):ℂ)).re ≤ ((sourceBlock6848XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6848+k) _ _ _
    (sourceBlock6848PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6848_actual_enclosure k hk)
    (sourceBlock6848TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6848Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6848XiPair k).1 := by
  decide +kernel

theorem sourceBlock6848Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6848Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6848XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6848XiPair k)).2 ≤
      sourceBlock6848Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6848_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6848+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6848+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6848Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6848+k) (sourceBlock6848XiPair k) _
    (sourceBlock6848Xi_enclosure k hk) (sourceBlock6848Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6848Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6880_bound (k : ℕ) (hk : k < 6880) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6848
  · exact sourceRoundedMidpoint_first6848_bound k h
  · have hsum : 6848+(k-6848) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6848_bound (k-6848) (by omega)

end ReciprocalXi
