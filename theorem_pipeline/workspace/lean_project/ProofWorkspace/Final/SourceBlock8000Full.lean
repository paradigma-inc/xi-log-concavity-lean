import ProofWorkspace.Final.SourceBlock7968Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8000DataFull
import ProofWorkspace.Final.EtaBlock8000Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8000XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8000+k) (sourceBlock8000PiPairs.getD k (0,0))
    (sourceEtaBatch8000Lower k, sourceEtaBatch8000Upper k)
    (sourceBlock8000TwoPairs.getD k (0,0))

theorem sourceBlock8000Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8000XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8000+k):ℂ)).re ∧
      (xi (xiGridArgument (8000+k):ℂ)).re ≤ ((sourceBlock8000XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8000+k) _ _ _
    (sourceBlock8000PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8000_actual_enclosure k hk)
    (sourceBlock8000TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8000Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8000XiPair k).1 := by
  decide +kernel

theorem sourceBlock8000Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8000Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8000XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8000XiPair k)).2 ≤
      sourceBlock8000Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8000_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8000+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8000+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8000Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8000+k) (sourceBlock8000XiPair k) _
    (sourceBlock8000Xi_enclosure k hk) (sourceBlock8000Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8000Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8032_bound (k : ℕ) (hk : k < 8032) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8000
  · exact sourceRoundedMidpoint_first8000_bound k h
  · have hsum : 8000+(k-8000) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8000_bound (k-8000) (by omega)

end ReciprocalXi
