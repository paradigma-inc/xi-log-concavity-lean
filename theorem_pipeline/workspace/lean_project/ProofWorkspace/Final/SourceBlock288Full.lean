import ProofWorkspace.Final.SourceBlock256Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock288DataFull
import ProofWorkspace.Final.EtaBlock288Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock288XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (288+k) (sourceBlock288PiPairs.getD k (0,0))
    (sourceEtaBatch288Lower k, sourceEtaBatch288Upper k)
    (sourceBlock288TwoPairs.getD k (0,0))

theorem sourceBlock288Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock288XiPair k).1:ℝ) ≤ (xi (xiGridArgument (288+k):ℂ)).re ∧
      (xi (xiGridArgument (288+k):ℂ)).re ≤ ((sourceBlock288XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (288+k) _ _ _
    (sourceBlock288PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch288_actual_enclosure k hk)
    (sourceBlock288TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock288Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock288XiPair k).1 := by
  decide +kernel

theorem sourceBlock288Reciprocal_check : ∀ k : Fin 32,
    sourceBlock288Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock288XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock288XiPair k)).2 ≤
      sourceBlock288Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block288_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((288+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (288+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock288Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (288+k) (sourceBlock288XiPair k) _
    (sourceBlock288Xi_enclosure k hk) (sourceBlock288Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock288Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first320_bound (k : ℕ) (hk : k < 320) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 288
  · exact sourceRoundedMidpoint_first288_bound k h
  · have hsum : 288+(k-288) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block288_bound (k-288) (by omega)

end ReciprocalXi
