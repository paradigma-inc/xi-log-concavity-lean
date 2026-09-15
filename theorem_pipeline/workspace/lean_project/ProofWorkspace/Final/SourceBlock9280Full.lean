import ProofWorkspace.Final.SourceBlock9248Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9280DataFull
import ProofWorkspace.Final.EtaBlock9280Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9280XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9280+k) (sourceBlock9280PiPairs.getD k (0,0))
    (sourceEtaBatch9280Lower k, sourceEtaBatch9280Upper k)
    (sourceBlock9280TwoPairs.getD k (0,0))

theorem sourceBlock9280Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9280XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9280+k):ℂ)).re ∧
      (xi (xiGridArgument (9280+k):ℂ)).re ≤ ((sourceBlock9280XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9280+k) _ _ _
    (sourceBlock9280PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9280_actual_enclosure k hk)
    (sourceBlock9280TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9280Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9280XiPair k).1 := by
  decide +kernel

theorem sourceBlock9280Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9280Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9280XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9280XiPair k)).2 ≤
      sourceBlock9280Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9280_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9280+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9280+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9280Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9280+k) (sourceBlock9280XiPair k) _
    (sourceBlock9280Xi_enclosure k hk) (sourceBlock9280Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9280Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9312_bound (k : ℕ) (hk : k < 9312) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9280
  · exact sourceRoundedMidpoint_first9280_bound k h
  · have hsum : 9280+(k-9280) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9280_bound (k-9280) (by omega)

end ReciprocalXi
