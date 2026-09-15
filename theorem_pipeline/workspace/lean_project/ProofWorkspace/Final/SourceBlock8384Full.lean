import ProofWorkspace.Final.SourceBlock8352Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8384DataFull
import ProofWorkspace.Final.EtaBlock8384Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8384XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8384+k) (sourceBlock8384PiPairs.getD k (0,0))
    (sourceEtaBatch8384Lower k, sourceEtaBatch8384Upper k)
    (sourceBlock8384TwoPairs.getD k (0,0))

theorem sourceBlock8384Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8384XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8384+k):ℂ)).re ∧
      (xi (xiGridArgument (8384+k):ℂ)).re ≤ ((sourceBlock8384XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8384+k) _ _ _
    (sourceBlock8384PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8384_actual_enclosure k hk)
    (sourceBlock8384TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8384Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8384XiPair k).1 := by
  decide +kernel

theorem sourceBlock8384Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8384Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8384XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8384XiPair k)).2 ≤
      sourceBlock8384Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8384_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8384+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8384+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8384Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8384+k) (sourceBlock8384XiPair k) _
    (sourceBlock8384Xi_enclosure k hk) (sourceBlock8384Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8384Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8416_bound (k : ℕ) (hk : k < 8416) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8384
  · exact sourceRoundedMidpoint_first8384_bound k h
  · have hsum : 8384+(k-8384) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8384_bound (k-8384) (by omega)

end ReciprocalXi
