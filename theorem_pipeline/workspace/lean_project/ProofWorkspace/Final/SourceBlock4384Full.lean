import ProofWorkspace.Final.SourceBlock4352Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4384DataFull
import ProofWorkspace.Final.EtaBlock4384Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4384XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4384+k) (sourceBlock4384PiPairs.getD k (0,0))
    (sourceEtaBatch4384Lower k, sourceEtaBatch4384Upper k)
    (sourceBlock4384TwoPairs.getD k (0,0))

theorem sourceBlock4384Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4384XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4384+k):ℂ)).re ∧
      (xi (xiGridArgument (4384+k):ℂ)).re ≤ ((sourceBlock4384XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4384+k) _ _ _
    (sourceBlock4384PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4384_actual_enclosure k hk)
    (sourceBlock4384TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4384Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4384XiPair k).1 := by
  decide +kernel

theorem sourceBlock4384Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4384Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4384XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4384XiPair k)).2 ≤
      sourceBlock4384Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4384_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4384+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4384+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4384Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4384+k) (sourceBlock4384XiPair k) _
    (sourceBlock4384Xi_enclosure k hk) (sourceBlock4384Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4384Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4416_bound (k : ℕ) (hk : k < 4416) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4384
  · exact sourceRoundedMidpoint_first4384_bound k h
  · have hsum : 4384+(k-4384) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4384_bound (k-4384) (by omega)

end ReciprocalXi
