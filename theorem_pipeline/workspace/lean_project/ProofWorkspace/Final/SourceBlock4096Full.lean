import ProofWorkspace.Final.SourceBlock4064Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4096DataFull
import ProofWorkspace.Final.EtaBlock4096Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4096XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4096+k) (sourceBlock4096PiPairs.getD k (0,0))
    (sourceEtaBatch4096Lower k, sourceEtaBatch4096Upper k)
    (sourceBlock4096TwoPairs.getD k (0,0))

theorem sourceBlock4096Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4096XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4096+k):ℂ)).re ∧
      (xi (xiGridArgument (4096+k):ℂ)).re ≤ ((sourceBlock4096XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4096+k) _ _ _
    (sourceBlock4096PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4096_actual_enclosure k hk)
    (sourceBlock4096TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4096Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4096XiPair k).1 := by
  decide +kernel

theorem sourceBlock4096Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4096Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4096XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4096XiPair k)).2 ≤
      sourceBlock4096Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4096_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4096+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4096+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4096Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4096+k) (sourceBlock4096XiPair k) _
    (sourceBlock4096Xi_enclosure k hk) (sourceBlock4096Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4096Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4128_bound (k : ℕ) (hk : k < 4128) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4096
  · exact sourceRoundedMidpoint_first4096_bound k h
  · have hsum : 4096+(k-4096) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4096_bound (k-4096) (by omega)

end ReciprocalXi
