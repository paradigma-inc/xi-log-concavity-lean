import ProofWorkspace.Final.SourceBlock8064Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8096DataFull
import ProofWorkspace.Final.EtaBlock8096Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8096XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8096+k) (sourceBlock8096PiPairs.getD k (0,0))
    (sourceEtaBatch8096Lower k, sourceEtaBatch8096Upper k)
    (sourceBlock8096TwoPairs.getD k (0,0))

theorem sourceBlock8096Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8096XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8096+k):ℂ)).re ∧
      (xi (xiGridArgument (8096+k):ℂ)).re ≤ ((sourceBlock8096XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8096+k) _ _ _
    (sourceBlock8096PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8096_actual_enclosure k hk)
    (sourceBlock8096TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8096Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8096XiPair k).1 := by
  decide +kernel

theorem sourceBlock8096Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8096Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8096XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8096XiPair k)).2 ≤
      sourceBlock8096Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8096_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8096+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8096+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8096Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8096+k) (sourceBlock8096XiPair k) _
    (sourceBlock8096Xi_enclosure k hk) (sourceBlock8096Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8096Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8128_bound (k : ℕ) (hk : k < 8128) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8096
  · exact sourceRoundedMidpoint_first8096_bound k h
  · have hsum : 8096+(k-8096) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8096_bound (k-8096) (by omega)

end ReciprocalXi
