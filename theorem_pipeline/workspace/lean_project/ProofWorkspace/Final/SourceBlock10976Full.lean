import ProofWorkspace.Final.SourceBlock10944Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10976DataFull
import ProofWorkspace.Final.EtaBlock10976Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10976XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10976+k) (sourceBlock10976PiPairs.getD k (0,0))
    (sourceEtaBatch10976Lower k, sourceEtaBatch10976Upper k)
    (sourceBlock10976TwoPairs.getD k (0,0))

theorem sourceBlock10976Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10976XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10976+k):ℂ)).re ∧
      (xi (xiGridArgument (10976+k):ℂ)).re ≤ ((sourceBlock10976XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10976+k) _ _ _
    (sourceBlock10976PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10976_actual_enclosure k hk)
    (sourceBlock10976TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10976Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10976XiPair k).1 := by
  decide +kernel

theorem sourceBlock10976Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10976Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10976XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10976XiPair k)).2 ≤
      sourceBlock10976Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10976_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10976+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10976+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10976Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10976+k) (sourceBlock10976XiPair k) _
    (sourceBlock10976Xi_enclosure k hk) (sourceBlock10976Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10976Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11008_bound (k : ℕ) (hk : k < 11008) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10976
  · exact sourceRoundedMidpoint_first10976_bound k h
  · have hsum : 10976+(k-10976) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10976_bound (k-10976) (by omega)

end ReciprocalXi
