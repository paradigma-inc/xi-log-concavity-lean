import ProofWorkspace.Final.SourceBlock4704Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4736DataFull
import ProofWorkspace.Final.EtaBlock4736Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4736XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4736+k) (sourceBlock4736PiPairs.getD k (0,0))
    (sourceEtaBatch4736Lower k, sourceEtaBatch4736Upper k)
    (sourceBlock4736TwoPairs.getD k (0,0))

theorem sourceBlock4736Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4736XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4736+k):ℂ)).re ∧
      (xi (xiGridArgument (4736+k):ℂ)).re ≤ ((sourceBlock4736XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4736+k) _ _ _
    (sourceBlock4736PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4736_actual_enclosure k hk)
    (sourceBlock4736TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4736Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4736XiPair k).1 := by
  decide +kernel

theorem sourceBlock4736Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4736Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4736XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4736XiPair k)).2 ≤
      sourceBlock4736Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4736_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4736+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4736+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4736Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4736+k) (sourceBlock4736XiPair k) _
    (sourceBlock4736Xi_enclosure k hk) (sourceBlock4736Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4736Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4768_bound (k : ℕ) (hk : k < 4768) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4736
  · exact sourceRoundedMidpoint_first4736_bound k h
  · have hsum : 4736+(k-4736) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4736_bound (k-4736) (by omega)

end ReciprocalXi
