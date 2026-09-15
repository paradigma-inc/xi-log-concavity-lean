import ProofWorkspace.Final.SourceBlock4512Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4544DataFull
import ProofWorkspace.Final.EtaBlock4544Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4544XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4544+k) (sourceBlock4544PiPairs.getD k (0,0))
    (sourceEtaBatch4544Lower k, sourceEtaBatch4544Upper k)
    (sourceBlock4544TwoPairs.getD k (0,0))

theorem sourceBlock4544Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4544XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4544+k):ℂ)).re ∧
      (xi (xiGridArgument (4544+k):ℂ)).re ≤ ((sourceBlock4544XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4544+k) _ _ _
    (sourceBlock4544PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4544_actual_enclosure k hk)
    (sourceBlock4544TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4544Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4544XiPair k).1 := by
  decide +kernel

theorem sourceBlock4544Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4544Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4544XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4544XiPair k)).2 ≤
      sourceBlock4544Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4544_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4544+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4544+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4544Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4544+k) (sourceBlock4544XiPair k) _
    (sourceBlock4544Xi_enclosure k hk) (sourceBlock4544Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4544Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4576_bound (k : ℕ) (hk : k < 4576) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4544
  · exact sourceRoundedMidpoint_first4544_bound k h
  · have hsum : 4544+(k-4544) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4544_bound (k-4544) (by omega)

end ReciprocalXi
