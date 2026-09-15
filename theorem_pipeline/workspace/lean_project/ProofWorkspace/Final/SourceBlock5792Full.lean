import ProofWorkspace.Final.SourceBlock5760Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5792DataFull
import ProofWorkspace.Final.EtaBlock5792Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5792XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5792+k) (sourceBlock5792PiPairs.getD k (0,0))
    (sourceEtaBatch5792Lower k, sourceEtaBatch5792Upper k)
    (sourceBlock5792TwoPairs.getD k (0,0))

theorem sourceBlock5792Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5792XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5792+k):ℂ)).re ∧
      (xi (xiGridArgument (5792+k):ℂ)).re ≤ ((sourceBlock5792XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5792+k) _ _ _
    (sourceBlock5792PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5792_actual_enclosure k hk)
    (sourceBlock5792TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5792Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5792XiPair k).1 := by
  decide +kernel

theorem sourceBlock5792Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5792Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5792XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5792XiPair k)).2 ≤
      sourceBlock5792Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5792_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5792+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5792+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5792Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5792+k) (sourceBlock5792XiPair k) _
    (sourceBlock5792Xi_enclosure k hk) (sourceBlock5792Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5792Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5824_bound (k : ℕ) (hk : k < 5824) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5792
  · exact sourceRoundedMidpoint_first5792_bound k h
  · have hsum : 5792+(k-5792) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5792_bound (k-5792) (by omega)

end ReciprocalXi
