import ProofWorkspace.Final.SourceBlock3712Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3744DataFull
import ProofWorkspace.Final.EtaBlock3744Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3744XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3744+k) (sourceBlock3744PiPairs.getD k (0,0))
    (sourceEtaBatch3744Lower k, sourceEtaBatch3744Upper k)
    (sourceBlock3744TwoPairs.getD k (0,0))

theorem sourceBlock3744Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3744XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3744+k):ℂ)).re ∧
      (xi (xiGridArgument (3744+k):ℂ)).re ≤ ((sourceBlock3744XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3744+k) _ _ _
    (sourceBlock3744PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3744_actual_enclosure k hk)
    (sourceBlock3744TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3744Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3744XiPair k).1 := by
  decide +kernel

theorem sourceBlock3744Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3744Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3744XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3744XiPair k)).2 ≤
      sourceBlock3744Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3744_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3744+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3744+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3744Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3744+k) (sourceBlock3744XiPair k) _
    (sourceBlock3744Xi_enclosure k hk) (sourceBlock3744Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3744Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3776_bound (k : ℕ) (hk : k < 3776) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3744
  · exact sourceRoundedMidpoint_first3744_bound k h
  · have hsum : 3744+(k-3744) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3744_bound (k-3744) (by omega)

end ReciprocalXi
