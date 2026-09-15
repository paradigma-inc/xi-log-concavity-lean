import ProofWorkspace.Final.SourceBlock3968Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4000DataFull
import ProofWorkspace.Final.EtaBlock4000Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4000XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4000+k) (sourceBlock4000PiPairs.getD k (0,0))
    (sourceEtaBatch4000Lower k, sourceEtaBatch4000Upper k)
    (sourceBlock4000TwoPairs.getD k (0,0))

theorem sourceBlock4000Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4000XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4000+k):ℂ)).re ∧
      (xi (xiGridArgument (4000+k):ℂ)).re ≤ ((sourceBlock4000XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4000+k) _ _ _
    (sourceBlock4000PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4000_actual_enclosure k hk)
    (sourceBlock4000TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4000Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4000XiPair k).1 := by
  decide +kernel

theorem sourceBlock4000Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4000Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4000XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4000XiPair k)).2 ≤
      sourceBlock4000Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4000_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4000+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4000+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4000Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4000+k) (sourceBlock4000XiPair k) _
    (sourceBlock4000Xi_enclosure k hk) (sourceBlock4000Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4000Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4032_bound (k : ℕ) (hk : k < 4032) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4000
  · exact sourceRoundedMidpoint_first4000_bound k h
  · have hsum : 4000+(k-4000) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4000_bound (k-4000) (by omega)

end ReciprocalXi
