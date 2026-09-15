import ProofWorkspace.Final.SourceBlock12864Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12896DataFull
import ProofWorkspace.Final.EtaBlock12896Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12896XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12896+k) (sourceBlock12896PiPairs.getD k (0,0))
    (sourceEtaBatch12896Lower k, sourceEtaBatch12896Upper k)
    (sourceBlock12896TwoPairs.getD k (0,0))

theorem sourceBlock12896Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12896XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12896+k):ℂ)).re ∧
      (xi (xiGridArgument (12896+k):ℂ)).re ≤ ((sourceBlock12896XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12896+k) _ _ _
    (sourceBlock12896PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12896_actual_enclosure k hk)
    (sourceBlock12896TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12896Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12896XiPair k).1 := by
  decide +kernel

theorem sourceBlock12896Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12896Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12896XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12896XiPair k)).2 ≤
      sourceBlock12896Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12896_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12896+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12896+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12896Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12896+k) (sourceBlock12896XiPair k) _
    (sourceBlock12896Xi_enclosure k hk) (sourceBlock12896Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12896Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12928_bound (k : ℕ) (hk : k < 12928) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12896
  · exact sourceRoundedMidpoint_first12896_bound k h
  · have hsum : 12896+(k-12896) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12896_bound (k-12896) (by omega)

end ReciprocalXi
