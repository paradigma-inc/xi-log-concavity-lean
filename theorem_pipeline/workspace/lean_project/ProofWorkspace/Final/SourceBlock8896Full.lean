import ProofWorkspace.Final.SourceBlock8864Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8896DataFull
import ProofWorkspace.Final.EtaBlock8896Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8896XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8896+k) (sourceBlock8896PiPairs.getD k (0,0))
    (sourceEtaBatch8896Lower k, sourceEtaBatch8896Upper k)
    (sourceBlock8896TwoPairs.getD k (0,0))

theorem sourceBlock8896Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8896XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8896+k):ℂ)).re ∧
      (xi (xiGridArgument (8896+k):ℂ)).re ≤ ((sourceBlock8896XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8896+k) _ _ _
    (sourceBlock8896PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8896_actual_enclosure k hk)
    (sourceBlock8896TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8896Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8896XiPair k).1 := by
  decide +kernel

theorem sourceBlock8896Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8896Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8896XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8896XiPair k)).2 ≤
      sourceBlock8896Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8896_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8896+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8896+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8896Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8896+k) (sourceBlock8896XiPair k) _
    (sourceBlock8896Xi_enclosure k hk) (sourceBlock8896Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8896Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8928_bound (k : ℕ) (hk : k < 8928) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8896
  · exact sourceRoundedMidpoint_first8896_bound k h
  · have hsum : 8896+(k-8896) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8896_bound (k-8896) (by omega)

end ReciprocalXi
