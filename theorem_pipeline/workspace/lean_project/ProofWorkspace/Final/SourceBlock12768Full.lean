import ProofWorkspace.Final.SourceBlock12736Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12768DataFull
import ProofWorkspace.Final.EtaBlock12768Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12768XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12768+k) (sourceBlock12768PiPairs.getD k (0,0))
    (sourceEtaBatch12768Lower k, sourceEtaBatch12768Upper k)
    (sourceBlock12768TwoPairs.getD k (0,0))

theorem sourceBlock12768Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12768XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12768+k):ℂ)).re ∧
      (xi (xiGridArgument (12768+k):ℂ)).re ≤ ((sourceBlock12768XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12768+k) _ _ _
    (sourceBlock12768PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12768_actual_enclosure k hk)
    (sourceBlock12768TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12768Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12768XiPair k).1 := by
  decide +kernel

theorem sourceBlock12768Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12768Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12768XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12768XiPair k)).2 ≤
      sourceBlock12768Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12768_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12768+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12768+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12768Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12768+k) (sourceBlock12768XiPair k) _
    (sourceBlock12768Xi_enclosure k hk) (sourceBlock12768Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12768Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12800_bound (k : ℕ) (hk : k < 12800) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12768
  · exact sourceRoundedMidpoint_first12768_bound k h
  · have hsum : 12768+(k-12768) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12768_bound (k-12768) (by omega)

end ReciprocalXi
