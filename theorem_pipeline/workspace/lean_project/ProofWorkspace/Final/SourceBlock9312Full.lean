import ProofWorkspace.Final.SourceBlock9280Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9312DataFull
import ProofWorkspace.Final.EtaBlock9312Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9312XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9312+k) (sourceBlock9312PiPairs.getD k (0,0))
    (sourceEtaBatch9312Lower k, sourceEtaBatch9312Upper k)
    (sourceBlock9312TwoPairs.getD k (0,0))

theorem sourceBlock9312Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9312XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9312+k):ℂ)).re ∧
      (xi (xiGridArgument (9312+k):ℂ)).re ≤ ((sourceBlock9312XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9312+k) _ _ _
    (sourceBlock9312PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9312_actual_enclosure k hk)
    (sourceBlock9312TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9312Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9312XiPair k).1 := by
  decide +kernel

theorem sourceBlock9312Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9312Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9312XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9312XiPair k)).2 ≤
      sourceBlock9312Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9312_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9312+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9312+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9312Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9312+k) (sourceBlock9312XiPair k) _
    (sourceBlock9312Xi_enclosure k hk) (sourceBlock9312Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9312Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9344_bound (k : ℕ) (hk : k < 9344) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9312
  · exact sourceRoundedMidpoint_first9312_bound k h
  · have hsum : 9312+(k-9312) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9312_bound (k-9312) (by omega)

end ReciprocalXi
