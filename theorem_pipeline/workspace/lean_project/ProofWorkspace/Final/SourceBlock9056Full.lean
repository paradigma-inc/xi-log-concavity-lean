import ProofWorkspace.Final.SourceBlock9024Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9056DataFull
import ProofWorkspace.Final.EtaBlock9056Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9056XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9056+k) (sourceBlock9056PiPairs.getD k (0,0))
    (sourceEtaBatch9056Lower k, sourceEtaBatch9056Upper k)
    (sourceBlock9056TwoPairs.getD k (0,0))

theorem sourceBlock9056Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9056XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9056+k):ℂ)).re ∧
      (xi (xiGridArgument (9056+k):ℂ)).re ≤ ((sourceBlock9056XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9056+k) _ _ _
    (sourceBlock9056PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9056_actual_enclosure k hk)
    (sourceBlock9056TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9056Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9056XiPair k).1 := by
  decide +kernel

theorem sourceBlock9056Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9056Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9056XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9056XiPair k)).2 ≤
      sourceBlock9056Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9056_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9056+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9056+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9056Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9056+k) (sourceBlock9056XiPair k) _
    (sourceBlock9056Xi_enclosure k hk) (sourceBlock9056Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9056Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9088_bound (k : ℕ) (hk : k < 9088) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9056
  · exact sourceRoundedMidpoint_first9056_bound k h
  · have hsum : 9056+(k-9056) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9056_bound (k-9056) (by omega)

end ReciprocalXi
