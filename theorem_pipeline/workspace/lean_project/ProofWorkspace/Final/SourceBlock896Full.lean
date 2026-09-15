import ProofWorkspace.Final.SourceBlock864Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock896DataFull
import ProofWorkspace.Final.EtaBlock896Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock896XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (896+k) (sourceBlock896PiPairs.getD k (0,0))
    (sourceEtaBatch896Lower k, sourceEtaBatch896Upper k)
    (sourceBlock896TwoPairs.getD k (0,0))

theorem sourceBlock896Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock896XiPair k).1:ℝ) ≤ (xi (xiGridArgument (896+k):ℂ)).re ∧
      (xi (xiGridArgument (896+k):ℂ)).re ≤ ((sourceBlock896XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (896+k) _ _ _
    (sourceBlock896PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch896_actual_enclosure k hk)
    (sourceBlock896TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock896Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock896XiPair k).1 := by
  decide +kernel

theorem sourceBlock896Reciprocal_check : ∀ k : Fin 32,
    sourceBlock896Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock896XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock896XiPair k)).2 ≤
      sourceBlock896Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block896_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((896+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (896+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock896Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (896+k) (sourceBlock896XiPair k) _
    (sourceBlock896Xi_enclosure k hk) (sourceBlock896Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock896Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first928_bound (k : ℕ) (hk : k < 928) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 896
  · exact sourceRoundedMidpoint_first896_bound k h
  · have hsum : 896+(k-896) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block896_bound (k-896) (by omega)

end ReciprocalXi
