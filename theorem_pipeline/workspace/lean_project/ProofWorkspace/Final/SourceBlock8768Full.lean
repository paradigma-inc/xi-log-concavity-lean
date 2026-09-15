import ProofWorkspace.Final.SourceBlock8736Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8768DataFull
import ProofWorkspace.Final.EtaBlock8768Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8768XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8768+k) (sourceBlock8768PiPairs.getD k (0,0))
    (sourceEtaBatch8768Lower k, sourceEtaBatch8768Upper k)
    (sourceBlock8768TwoPairs.getD k (0,0))

theorem sourceBlock8768Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8768XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8768+k):ℂ)).re ∧
      (xi (xiGridArgument (8768+k):ℂ)).re ≤ ((sourceBlock8768XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8768+k) _ _ _
    (sourceBlock8768PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8768_actual_enclosure k hk)
    (sourceBlock8768TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8768Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8768XiPair k).1 := by
  decide +kernel

theorem sourceBlock8768Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8768Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8768XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8768XiPair k)).2 ≤
      sourceBlock8768Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8768_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8768+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8768+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8768Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8768+k) (sourceBlock8768XiPair k) _
    (sourceBlock8768Xi_enclosure k hk) (sourceBlock8768Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8768Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8800_bound (k : ℕ) (hk : k < 8800) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8768
  · exact sourceRoundedMidpoint_first8768_bound k h
  · have hsum : 8768+(k-8768) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8768_bound (k-8768) (by omega)

end ReciprocalXi
