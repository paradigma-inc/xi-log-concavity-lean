import ProofWorkspace.Final.SourceBlock4864Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4896DataFull
import ProofWorkspace.Final.EtaBlock4896Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4896XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4896+k) (sourceBlock4896PiPairs.getD k (0,0))
    (sourceEtaBatch4896Lower k, sourceEtaBatch4896Upper k)
    (sourceBlock4896TwoPairs.getD k (0,0))

theorem sourceBlock4896Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4896XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4896+k):ℂ)).re ∧
      (xi (xiGridArgument (4896+k):ℂ)).re ≤ ((sourceBlock4896XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4896+k) _ _ _
    (sourceBlock4896PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4896_actual_enclosure k hk)
    (sourceBlock4896TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4896Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4896XiPair k).1 := by
  decide +kernel

theorem sourceBlock4896Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4896Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4896XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4896XiPair k)).2 ≤
      sourceBlock4896Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4896_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4896+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4896+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4896Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4896+k) (sourceBlock4896XiPair k) _
    (sourceBlock4896Xi_enclosure k hk) (sourceBlock4896Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4896Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4928_bound (k : ℕ) (hk : k < 4928) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4896
  · exact sourceRoundedMidpoint_first4896_bound k h
  · have hsum : 4896+(k-4896) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4896_bound (k-4896) (by omega)

end ReciprocalXi
