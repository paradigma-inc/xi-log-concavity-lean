import ProofWorkspace.Final.SourceBlock4256Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4288DataFull
import ProofWorkspace.Final.EtaBlock4288Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4288XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4288+k) (sourceBlock4288PiPairs.getD k (0,0))
    (sourceEtaBatch4288Lower k, sourceEtaBatch4288Upper k)
    (sourceBlock4288TwoPairs.getD k (0,0))

theorem sourceBlock4288Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4288XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4288+k):ℂ)).re ∧
      (xi (xiGridArgument (4288+k):ℂ)).re ≤ ((sourceBlock4288XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4288+k) _ _ _
    (sourceBlock4288PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4288_actual_enclosure k hk)
    (sourceBlock4288TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4288Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4288XiPair k).1 := by
  decide +kernel

theorem sourceBlock4288Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4288Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4288XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4288XiPair k)).2 ≤
      sourceBlock4288Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4288_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4288+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4288+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4288Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4288+k) (sourceBlock4288XiPair k) _
    (sourceBlock4288Xi_enclosure k hk) (sourceBlock4288Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4288Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4320_bound (k : ℕ) (hk : k < 4320) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4288
  · exact sourceRoundedMidpoint_first4288_bound k h
  · have hsum : 4288+(k-4288) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4288_bound (k-4288) (by omega)

end ReciprocalXi
