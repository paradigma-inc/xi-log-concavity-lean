import ProofWorkspace.Final.SourceBlock12512Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12544DataFull
import ProofWorkspace.Final.EtaBlock12544Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12544XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12544+k) (sourceBlock12544PiPairs.getD k (0,0))
    (sourceEtaBatch12544Lower k, sourceEtaBatch12544Upper k)
    (sourceBlock12544TwoPairs.getD k (0,0))

theorem sourceBlock12544Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12544XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12544+k):ℂ)).re ∧
      (xi (xiGridArgument (12544+k):ℂ)).re ≤ ((sourceBlock12544XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12544+k) _ _ _
    (sourceBlock12544PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12544_actual_enclosure k hk)
    (sourceBlock12544TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12544Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12544XiPair k).1 := by
  decide +kernel

theorem sourceBlock12544Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12544Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12544XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12544XiPair k)).2 ≤
      sourceBlock12544Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12544_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12544+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12544+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12544Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12544+k) (sourceBlock12544XiPair k) _
    (sourceBlock12544Xi_enclosure k hk) (sourceBlock12544Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12544Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12576_bound (k : ℕ) (hk : k < 12576) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12544
  · exact sourceRoundedMidpoint_first12544_bound k h
  · have hsum : 12544+(k-12544) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12544_bound (k-12544) (by omega)

end ReciprocalXi
