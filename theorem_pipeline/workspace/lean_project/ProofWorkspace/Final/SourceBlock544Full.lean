import ProofWorkspace.Final.SourceBlock512Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock544DataFull
import ProofWorkspace.Final.EtaBlock544Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock544XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (544+k) (sourceBlock544PiPairs.getD k (0,0))
    (sourceEtaBatch544Lower k, sourceEtaBatch544Upper k)
    (sourceBlock544TwoPairs.getD k (0,0))

theorem sourceBlock544Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock544XiPair k).1:ℝ) ≤ (xi (xiGridArgument (544+k):ℂ)).re ∧
      (xi (xiGridArgument (544+k):ℂ)).re ≤ ((sourceBlock544XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (544+k) _ _ _
    (sourceBlock544PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch544_actual_enclosure k hk)
    (sourceBlock544TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock544Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock544XiPair k).1 := by
  decide +kernel

theorem sourceBlock544Reciprocal_check : ∀ k : Fin 32,
    sourceBlock544Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock544XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock544XiPair k)).2 ≤
      sourceBlock544Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block544_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((544+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (544+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock544Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (544+k) (sourceBlock544XiPair k) _
    (sourceBlock544Xi_enclosure k hk) (sourceBlock544Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock544Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first576_bound (k : ℕ) (hk : k < 576) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 544
  · exact sourceRoundedMidpoint_first544_bound k h
  · have hsum : 544+(k-544) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block544_bound (k-544) (by omega)

end ReciprocalXi
