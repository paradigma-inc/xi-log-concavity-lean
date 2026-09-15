import ProofWorkspace.Final.SourceBlock6944Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6976DataFull
import ProofWorkspace.Final.EtaBlock6976Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6976XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6976+k) (sourceBlock6976PiPairs.getD k (0,0))
    (sourceEtaBatch6976Lower k, sourceEtaBatch6976Upper k)
    (sourceBlock6976TwoPairs.getD k (0,0))

theorem sourceBlock6976Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6976XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6976+k):ℂ)).re ∧
      (xi (xiGridArgument (6976+k):ℂ)).re ≤ ((sourceBlock6976XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6976+k) _ _ _
    (sourceBlock6976PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6976_actual_enclosure k hk)
    (sourceBlock6976TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6976Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6976XiPair k).1 := by
  decide +kernel

theorem sourceBlock6976Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6976Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6976XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6976XiPair k)).2 ≤
      sourceBlock6976Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6976_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6976+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6976+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6976Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6976+k) (sourceBlock6976XiPair k) _
    (sourceBlock6976Xi_enclosure k hk) (sourceBlock6976Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6976Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7008_bound (k : ℕ) (hk : k < 7008) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6976
  · exact sourceRoundedMidpoint_first6976_bound k h
  · have hsum : 6976+(k-6976) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6976_bound (k-6976) (by omega)

end ReciprocalXi
