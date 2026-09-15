import ProofWorkspace.Final.SourceBlock4416Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4448DataFull
import ProofWorkspace.Final.EtaBlock4448Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4448XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4448+k) (sourceBlock4448PiPairs.getD k (0,0))
    (sourceEtaBatch4448Lower k, sourceEtaBatch4448Upper k)
    (sourceBlock4448TwoPairs.getD k (0,0))

theorem sourceBlock4448Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4448XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4448+k):ℂ)).re ∧
      (xi (xiGridArgument (4448+k):ℂ)).re ≤ ((sourceBlock4448XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4448+k) _ _ _
    (sourceBlock4448PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4448_actual_enclosure k hk)
    (sourceBlock4448TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4448Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4448XiPair k).1 := by
  decide +kernel

theorem sourceBlock4448Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4448Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4448XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4448XiPair k)).2 ≤
      sourceBlock4448Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4448_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4448+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4448+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4448Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4448+k) (sourceBlock4448XiPair k) _
    (sourceBlock4448Xi_enclosure k hk) (sourceBlock4448Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4448Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4480_bound (k : ℕ) (hk : k < 4480) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4448
  · exact sourceRoundedMidpoint_first4448_bound k h
  · have hsum : 4448+(k-4448) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4448_bound (k-4448) (by omega)

end ReciprocalXi
