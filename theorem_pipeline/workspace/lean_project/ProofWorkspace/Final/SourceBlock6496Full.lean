import ProofWorkspace.Final.SourceBlock6464Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6496DataFull
import ProofWorkspace.Final.EtaBlock6496Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6496XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6496+k) (sourceBlock6496PiPairs.getD k (0,0))
    (sourceEtaBatch6496Lower k, sourceEtaBatch6496Upper k)
    (sourceBlock6496TwoPairs.getD k (0,0))

theorem sourceBlock6496Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6496XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6496+k):ℂ)).re ∧
      (xi (xiGridArgument (6496+k):ℂ)).re ≤ ((sourceBlock6496XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6496+k) _ _ _
    (sourceBlock6496PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6496_actual_enclosure k hk)
    (sourceBlock6496TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6496Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6496XiPair k).1 := by
  decide +kernel

theorem sourceBlock6496Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6496Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6496XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6496XiPair k)).2 ≤
      sourceBlock6496Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6496_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6496+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6496+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6496Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6496+k) (sourceBlock6496XiPair k) _
    (sourceBlock6496Xi_enclosure k hk) (sourceBlock6496Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6496Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6528_bound (k : ℕ) (hk : k < 6528) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6496
  · exact sourceRoundedMidpoint_first6496_bound k h
  · have hsum : 6496+(k-6496) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6496_bound (k-6496) (by omega)

end ReciprocalXi
