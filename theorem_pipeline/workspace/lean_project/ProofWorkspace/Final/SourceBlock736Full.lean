import ProofWorkspace.Final.SourceBlock704Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock736DataFull
import ProofWorkspace.Final.EtaBlock736Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock736XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (736+k) (sourceBlock736PiPairs.getD k (0,0))
    (sourceEtaBatch736Lower k, sourceEtaBatch736Upper k)
    (sourceBlock736TwoPairs.getD k (0,0))

theorem sourceBlock736Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock736XiPair k).1:ℝ) ≤ (xi (xiGridArgument (736+k):ℂ)).re ∧
      (xi (xiGridArgument (736+k):ℂ)).re ≤ ((sourceBlock736XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (736+k) _ _ _
    (sourceBlock736PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch736_actual_enclosure k hk)
    (sourceBlock736TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock736Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock736XiPair k).1 := by
  decide +kernel

theorem sourceBlock736Reciprocal_check : ∀ k : Fin 32,
    sourceBlock736Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock736XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock736XiPair k)).2 ≤
      sourceBlock736Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block736_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((736+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (736+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock736Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (736+k) (sourceBlock736XiPair k) _
    (sourceBlock736Xi_enclosure k hk) (sourceBlock736Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock736Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first768_bound (k : ℕ) (hk : k < 768) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 736
  · exact sourceRoundedMidpoint_first736_bound k h
  · have hsum : 736+(k-736) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block736_bound (k-736) (by omega)

end ReciprocalXi
