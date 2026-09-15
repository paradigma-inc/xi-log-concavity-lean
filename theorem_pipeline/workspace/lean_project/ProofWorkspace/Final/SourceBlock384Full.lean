import ProofWorkspace.Final.SourceBlock352Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock384DataFull
import ProofWorkspace.Final.EtaBlock384Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock384XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (384+k) (sourceBlock384PiPairs.getD k (0,0))
    (sourceEtaBatch384Lower k, sourceEtaBatch384Upper k)
    (sourceBlock384TwoPairs.getD k (0,0))

theorem sourceBlock384Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock384XiPair k).1:ℝ) ≤ (xi (xiGridArgument (384+k):ℂ)).re ∧
      (xi (xiGridArgument (384+k):ℂ)).re ≤ ((sourceBlock384XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (384+k) _ _ _
    (sourceBlock384PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch384_actual_enclosure k hk)
    (sourceBlock384TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock384Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock384XiPair k).1 := by
  decide +kernel

theorem sourceBlock384Reciprocal_check : ∀ k : Fin 32,
    sourceBlock384Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock384XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock384XiPair k)).2 ≤
      sourceBlock384Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block384_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((384+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (384+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock384Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (384+k) (sourceBlock384XiPair k) _
    (sourceBlock384Xi_enclosure k hk) (sourceBlock384Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock384Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first416_bound (k : ℕ) (hk : k < 416) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 384
  · exact sourceRoundedMidpoint_first384_bound k h
  · have hsum : 384+(k-384) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block384_bound (k-384) (by omega)

end ReciprocalXi
