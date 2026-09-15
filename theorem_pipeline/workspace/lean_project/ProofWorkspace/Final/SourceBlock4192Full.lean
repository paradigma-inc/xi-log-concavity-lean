import ProofWorkspace.Final.SourceBlock4160Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4192DataFull
import ProofWorkspace.Final.EtaBlock4192Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4192XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4192+k) (sourceBlock4192PiPairs.getD k (0,0))
    (sourceEtaBatch4192Lower k, sourceEtaBatch4192Upper k)
    (sourceBlock4192TwoPairs.getD k (0,0))

theorem sourceBlock4192Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4192XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4192+k):ℂ)).re ∧
      (xi (xiGridArgument (4192+k):ℂ)).re ≤ ((sourceBlock4192XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4192+k) _ _ _
    (sourceBlock4192PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4192_actual_enclosure k hk)
    (sourceBlock4192TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4192Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4192XiPair k).1 := by
  decide +kernel

theorem sourceBlock4192Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4192Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4192XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4192XiPair k)).2 ≤
      sourceBlock4192Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4192_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4192+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4192+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4192Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4192+k) (sourceBlock4192XiPair k) _
    (sourceBlock4192Xi_enclosure k hk) (sourceBlock4192Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4192Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4224_bound (k : ℕ) (hk : k < 4224) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4192
  · exact sourceRoundedMidpoint_first4192_bound k h
  · have hsum : 4192+(k-4192) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4192_bound (k-4192) (by omega)

end ReciprocalXi
