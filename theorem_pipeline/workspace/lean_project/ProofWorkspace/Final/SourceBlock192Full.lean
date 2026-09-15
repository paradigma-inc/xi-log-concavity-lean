import ProofWorkspace.Final.SourceBlock160Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock192DataFull
import ProofWorkspace.Final.EtaBlock192Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock192XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (192+k) (sourceBlock192PiPairs.getD k (0,0))
    (sourceEtaBatch192Lower k, sourceEtaBatch192Upper k)
    (sourceBlock192TwoPairs.getD k (0,0))

theorem sourceBlock192Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock192XiPair k).1:ℝ) ≤ (xi (xiGridArgument (192+k):ℂ)).re ∧
      (xi (xiGridArgument (192+k):ℂ)).re ≤ ((sourceBlock192XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (192+k) _ _ _
    (sourceBlock192PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch192_actual_enclosure k hk)
    (sourceBlock192TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock192Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock192XiPair k).1 := by
  decide +kernel

theorem sourceBlock192Reciprocal_check : ∀ k : Fin 32,
    sourceBlock192Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock192XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock192XiPair k)).2 ≤
      sourceBlock192Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block192_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((192+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (192+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock192Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (192+k) (sourceBlock192XiPair k) _
    (sourceBlock192Xi_enclosure k hk) (sourceBlock192Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock192Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first224_bound (k : ℕ) (hk : k < 224) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 192
  · exact sourceRoundedMidpoint_first192_bound k h
  · have hsum : 192+(k-192) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block192_bound (k-192) (by omega)

end ReciprocalXi
