import ProofWorkspace.Final.SourceBlock1952Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock1984DataFull
import ProofWorkspace.Final.EtaBlock1984Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock1984XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (1984+k) (sourceBlock1984PiPairs.getD k (0,0))
    (sourceEtaBatch1984Lower k, sourceEtaBatch1984Upper k)
    (sourceBlock1984TwoPairs.getD k (0,0))

theorem sourceBlock1984Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock1984XiPair k).1:ℝ) ≤ (xi (xiGridArgument (1984+k):ℂ)).re ∧
      (xi (xiGridArgument (1984+k):ℂ)).re ≤ ((sourceBlock1984XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (1984+k) _ _ _
    (sourceBlock1984PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch1984_actual_enclosure k hk)
    (sourceBlock1984TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock1984Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock1984XiPair k).1 := by
  decide +kernel

theorem sourceBlock1984Reciprocal_check : ∀ k : Fin 32,
    sourceBlock1984Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock1984XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock1984XiPair k)).2 ≤
      sourceBlock1984Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block1984_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((1984+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (1984+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock1984Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (1984+k) (sourceBlock1984XiPair k) _
    (sourceBlock1984Xi_enclosure k hk) (sourceBlock1984Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock1984Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first2016_bound (k : ℕ) (hk : k < 2016) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 1984
  · exact sourceRoundedMidpoint_first1984_bound k h
  · have hsum : 1984+(k-1984) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block1984_bound (k-1984) (by omega)

end ReciprocalXi
