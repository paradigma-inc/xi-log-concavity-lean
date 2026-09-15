import ProofWorkspace.Final.SourceBlock10464Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10496DataFull
import ProofWorkspace.Final.EtaBlock10496Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10496XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10496+k) (sourceBlock10496PiPairs.getD k (0,0))
    (sourceEtaBatch10496Lower k, sourceEtaBatch10496Upper k)
    (sourceBlock10496TwoPairs.getD k (0,0))

theorem sourceBlock10496Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10496XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10496+k):ℂ)).re ∧
      (xi (xiGridArgument (10496+k):ℂ)).re ≤ ((sourceBlock10496XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10496+k) _ _ _
    (sourceBlock10496PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10496_actual_enclosure k hk)
    (sourceBlock10496TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10496Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10496XiPair k).1 := by
  decide +kernel

theorem sourceBlock10496Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10496Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10496XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10496XiPair k)).2 ≤
      sourceBlock10496Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10496_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10496+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10496+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10496Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10496+k) (sourceBlock10496XiPair k) _
    (sourceBlock10496Xi_enclosure k hk) (sourceBlock10496Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10496Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10528_bound (k : ℕ) (hk : k < 10528) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10496
  · exact sourceRoundedMidpoint_first10496_bound k h
  · have hsum : 10496+(k-10496) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10496_bound (k-10496) (by omega)

end ReciprocalXi
