import ProofWorkspace.Final.SourceBlock3904Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3936DataFull
import ProofWorkspace.Final.EtaBlock3936Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3936XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3936+k) (sourceBlock3936PiPairs.getD k (0,0))
    (sourceEtaBatch3936Lower k, sourceEtaBatch3936Upper k)
    (sourceBlock3936TwoPairs.getD k (0,0))

theorem sourceBlock3936Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3936XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3936+k):ℂ)).re ∧
      (xi (xiGridArgument (3936+k):ℂ)).re ≤ ((sourceBlock3936XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3936+k) _ _ _
    (sourceBlock3936PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3936_actual_enclosure k hk)
    (sourceBlock3936TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3936Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3936XiPair k).1 := by
  decide +kernel

theorem sourceBlock3936Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3936Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3936XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3936XiPair k)).2 ≤
      sourceBlock3936Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3936_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3936+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3936+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3936Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3936+k) (sourceBlock3936XiPair k) _
    (sourceBlock3936Xi_enclosure k hk) (sourceBlock3936Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3936Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3968_bound (k : ℕ) (hk : k < 3968) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3936
  · exact sourceRoundedMidpoint_first3936_bound k h
  · have hsum : 3936+(k-3936) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3936_bound (k-3936) (by omega)

end ReciprocalXi
