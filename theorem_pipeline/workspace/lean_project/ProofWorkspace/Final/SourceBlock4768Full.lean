import ProofWorkspace.Final.SourceBlock4736Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4768DataFull
import ProofWorkspace.Final.EtaBlock4768Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4768XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4768+k) (sourceBlock4768PiPairs.getD k (0,0))
    (sourceEtaBatch4768Lower k, sourceEtaBatch4768Upper k)
    (sourceBlock4768TwoPairs.getD k (0,0))

theorem sourceBlock4768Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4768XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4768+k):ℂ)).re ∧
      (xi (xiGridArgument (4768+k):ℂ)).re ≤ ((sourceBlock4768XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4768+k) _ _ _
    (sourceBlock4768PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4768_actual_enclosure k hk)
    (sourceBlock4768TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4768Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4768XiPair k).1 := by
  decide +kernel

theorem sourceBlock4768Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4768Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4768XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4768XiPair k)).2 ≤
      sourceBlock4768Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4768_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4768+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4768+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4768Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4768+k) (sourceBlock4768XiPair k) _
    (sourceBlock4768Xi_enclosure k hk) (sourceBlock4768Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4768Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4800_bound (k : ℕ) (hk : k < 4800) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4768
  · exact sourceRoundedMidpoint_first4768_bound k h
  · have hsum : 4768+(k-4768) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4768_bound (k-4768) (by omega)

end ReciprocalXi
