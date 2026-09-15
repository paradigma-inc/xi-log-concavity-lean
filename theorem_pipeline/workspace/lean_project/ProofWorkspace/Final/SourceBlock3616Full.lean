import ProofWorkspace.Final.SourceBlock3584Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock3616DataFull
import ProofWorkspace.Final.EtaBlock3616Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock3616XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (3616+k) (sourceBlock3616PiPairs.getD k (0,0))
    (sourceEtaBatch3616Lower k, sourceEtaBatch3616Upper k)
    (sourceBlock3616TwoPairs.getD k (0,0))

theorem sourceBlock3616Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock3616XiPair k).1:ℝ) ≤ (xi (xiGridArgument (3616+k):ℂ)).re ∧
      (xi (xiGridArgument (3616+k):ℂ)).re ≤ ((sourceBlock3616XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (3616+k) _ _ _
    (sourceBlock3616PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch3616_actual_enclosure k hk)
    (sourceBlock3616TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock3616Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock3616XiPair k).1 := by
  decide +kernel

theorem sourceBlock3616Reciprocal_check : ∀ k : Fin 32,
    sourceBlock3616Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock3616XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock3616XiPair k)).2 ≤
      sourceBlock3616Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block3616_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((3616+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (3616+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock3616Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (3616+k) (sourceBlock3616XiPair k) _
    (sourceBlock3616Xi_enclosure k hk) (sourceBlock3616Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock3616Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first3648_bound (k : ℕ) (hk : k < 3648) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 3616
  · exact sourceRoundedMidpoint_first3616_bound k h
  · have hsum : 3616+(k-3616) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block3616_bound (k-3616) (by omega)

end ReciprocalXi
