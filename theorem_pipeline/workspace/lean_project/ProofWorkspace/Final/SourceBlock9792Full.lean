import ProofWorkspace.Final.SourceBlock9760Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9792DataFull
import ProofWorkspace.Final.EtaBlock9792Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9792XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9792+k) (sourceBlock9792PiPairs.getD k (0,0))
    (sourceEtaBatch9792Lower k, sourceEtaBatch9792Upper k)
    (sourceBlock9792TwoPairs.getD k (0,0))

theorem sourceBlock9792Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9792XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9792+k):ℂ)).re ∧
      (xi (xiGridArgument (9792+k):ℂ)).re ≤ ((sourceBlock9792XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9792+k) _ _ _
    (sourceBlock9792PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9792_actual_enclosure k hk)
    (sourceBlock9792TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9792Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9792XiPair k).1 := by
  decide +kernel

theorem sourceBlock9792Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9792Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9792XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9792XiPair k)).2 ≤
      sourceBlock9792Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9792_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9792+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9792+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9792Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9792+k) (sourceBlock9792XiPair k) _
    (sourceBlock9792Xi_enclosure k hk) (sourceBlock9792Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9792Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9824_bound (k : ℕ) (hk : k < 9824) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9792
  · exact sourceRoundedMidpoint_first9792_bound k h
  · have hsum : 9792+(k-9792) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9792_bound (k-9792) (by omega)

end ReciprocalXi
