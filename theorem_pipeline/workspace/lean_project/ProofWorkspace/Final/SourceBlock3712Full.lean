import ProofWorkspace.Final.SourceBlock3680Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3712DataFull
import ProofWorkspace.Final.EtaBlock3712Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3712XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3712+k) (sourceBlock3712PiPairs.getD k (0,0))
    (sourceEtaBatch3712Lower k, sourceEtaBatch3712Upper k)
    (sourceBlock3712TwoPairs.getD k (0,0))

theorem sourceBlock3712Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3712XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3712+k):ℂ)).re ∧
      (xi (xiGridArgument (3712+k):ℂ)).re ≤ ((sourceBlock3712XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3712+k) _ _ _
    (sourceBlock3712PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3712_actual_enclosure k hk)
    (sourceBlock3712TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3712Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3712XiPair k).1 := by
  decide +kernel

theorem sourceBlock3712Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3712Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3712XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3712XiPair k)).2 ≤
      sourceBlock3712Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3712_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3712+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3712+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3712Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3712+k) (sourceBlock3712XiPair k) _
    (sourceBlock3712Xi_enclosure k hk) (sourceBlock3712Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3712Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3744_bound (k : ℕ) (hk : k < 3744) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3712
  · exact sourceRoundedMidpoint_first3712_bound k h
  · have hsum : 3712+(k-3712) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3712_bound (k-3712) (by omega)

end ReciprocalXi
