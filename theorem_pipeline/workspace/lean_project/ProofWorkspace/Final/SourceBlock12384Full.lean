import ProofWorkspace.Final.SourceBlock12352Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12384DataFull
import ProofWorkspace.Final.EtaBlock12384Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12384XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12384+k) (sourceBlock12384PiPairs.getD k (0,0))
    (sourceEtaBatch12384Lower k, sourceEtaBatch12384Upper k)
    (sourceBlock12384TwoPairs.getD k (0,0))

theorem sourceBlock12384Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12384XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12384+k):ℂ)).re ∧
      (xi (xiGridArgument (12384+k):ℂ)).re ≤ ((sourceBlock12384XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12384+k) _ _ _
    (sourceBlock12384PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12384_actual_enclosure k hk)
    (sourceBlock12384TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12384Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12384XiPair k).1 := by
  decide +kernel

theorem sourceBlock12384Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12384Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12384XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12384XiPair k)).2 ≤
      sourceBlock12384Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12384_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12384+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12384+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12384Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12384+k) (sourceBlock12384XiPair k) _
    (sourceBlock12384Xi_enclosure k hk) (sourceBlock12384Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12384Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12416_bound (k : ℕ) (hk : k < 12416) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12384
  · exact sourceRoundedMidpoint_first12384_bound k h
  · have hsum : 12384+(k-12384) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12384_bound (k-12384) (by omega)

end ReciprocalXi
