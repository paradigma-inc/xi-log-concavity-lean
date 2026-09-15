import ProofWorkspace.Final.SourceBlock9952Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9984DataFull
import ProofWorkspace.Final.EtaBlock9984Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9984XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9984+k) (sourceBlock9984PiPairs.getD k (0,0))
    (sourceEtaBatch9984Lower k, sourceEtaBatch9984Upper k)
    (sourceBlock9984TwoPairs.getD k (0,0))

theorem sourceBlock9984Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9984XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9984+k):ℂ)).re ∧
      (xi (xiGridArgument (9984+k):ℂ)).re ≤ ((sourceBlock9984XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9984+k) _ _ _
    (sourceBlock9984PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9984_actual_enclosure k hk)
    (sourceBlock9984TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9984Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9984XiPair k).1 := by
  decide +kernel

theorem sourceBlock9984Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9984Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9984XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9984XiPair k)).2 ≤
      sourceBlock9984Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9984_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9984+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9984+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9984Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9984+k) (sourceBlock9984XiPair k) _
    (sourceBlock9984Xi_enclosure k hk) (sourceBlock9984Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9984Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10016_bound (k : ℕ) (hk : k < 10016) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9984
  · exact sourceRoundedMidpoint_first9984_bound k h
  · have hsum : 9984+(k-9984) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9984_bound (k-9984) (by omega)

end ReciprocalXi
