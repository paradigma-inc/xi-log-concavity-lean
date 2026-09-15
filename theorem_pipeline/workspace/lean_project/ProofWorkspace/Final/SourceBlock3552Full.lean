import ProofWorkspace.Final.SourceBlock3520Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3552DataFull
import ProofWorkspace.Final.EtaBlock3552Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3552XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3552+k) (sourceBlock3552PiPairs.getD k (0,0))
    (sourceEtaBatch3552Lower k, sourceEtaBatch3552Upper k)
    (sourceBlock3552TwoPairs.getD k (0,0))

theorem sourceBlock3552Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3552XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3552+k):ℂ)).re ∧
      (xi (xiGridArgument (3552+k):ℂ)).re ≤ ((sourceBlock3552XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3552+k) _ _ _
    (sourceBlock3552PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3552_actual_enclosure k hk)
    (sourceBlock3552TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3552Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3552XiPair k).1 := by
  decide +kernel

theorem sourceBlock3552Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3552Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3552XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3552XiPair k)).2 ≤
      sourceBlock3552Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3552_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3552+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3552+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3552Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3552+k) (sourceBlock3552XiPair k) _
    (sourceBlock3552Xi_enclosure k hk) (sourceBlock3552Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3552Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3584_bound (k : ℕ) (hk : k < 3584) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3552
  · exact sourceRoundedMidpoint_first3552_bound k h
  · have hsum : 3552+(k-3552) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3552_bound (k-3552) (by omega)

end ReciprocalXi
