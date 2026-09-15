import ProofWorkspace.Final.SourceBlock12064Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12096DataFull
import ProofWorkspace.Final.EtaBlock12096Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12096XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12096+k) (sourceBlock12096PiPairs.getD k (0,0))
    (sourceEtaBatch12096Lower k, sourceEtaBatch12096Upper k)
    (sourceBlock12096TwoPairs.getD k (0,0))

theorem sourceBlock12096Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12096XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12096+k):ℂ)).re ∧
      (xi (xiGridArgument (12096+k):ℂ)).re ≤ ((sourceBlock12096XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12096+k) _ _ _
    (sourceBlock12096PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12096_actual_enclosure k hk)
    (sourceBlock12096TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12096Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12096XiPair k).1 := by
  decide +kernel

theorem sourceBlock12096Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12096Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12096XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12096XiPair k)).2 ≤
      sourceBlock12096Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12096_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12096+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12096+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12096Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12096+k) (sourceBlock12096XiPair k) _
    (sourceBlock12096Xi_enclosure k hk) (sourceBlock12096Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12096Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12128_bound (k : ℕ) (hk : k < 12128) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12096
  · exact sourceRoundedMidpoint_first12096_bound k h
  · have hsum : 12096+(k-12096) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12096_bound (k-12096) (by omega)

end ReciprocalXi
