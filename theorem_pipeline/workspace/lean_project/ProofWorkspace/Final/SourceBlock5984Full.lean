import ProofWorkspace.Final.SourceBlock5952Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5984DataFull
import ProofWorkspace.Final.EtaBlock5984Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5984XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5984+k) (sourceBlock5984PiPairs.getD k (0,0))
    (sourceEtaBatch5984Lower k, sourceEtaBatch5984Upper k)
    (sourceBlock5984TwoPairs.getD k (0,0))

theorem sourceBlock5984Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5984XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5984+k):ℂ)).re ∧
      (xi (xiGridArgument (5984+k):ℂ)).re ≤ ((sourceBlock5984XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5984+k) _ _ _
    (sourceBlock5984PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5984_actual_enclosure k hk)
    (sourceBlock5984TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5984Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5984XiPair k).1 := by
  decide +kernel

theorem sourceBlock5984Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5984Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5984XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5984XiPair k)).2 ≤
      sourceBlock5984Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5984_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5984+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5984+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5984Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5984+k) (sourceBlock5984XiPair k) _
    (sourceBlock5984Xi_enclosure k hk) (sourceBlock5984Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5984Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6016_bound (k : ℕ) (hk : k < 6016) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5984
  · exact sourceRoundedMidpoint_first5984_bound k h
  · have hsum : 5984+(k-5984) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5984_bound (k-5984) (by omega)

end ReciprocalXi
