import ProofWorkspace.Final.SourceBlock6432Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6464DataFull
import ProofWorkspace.Final.EtaBlock6464Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6464XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6464+k) (sourceBlock6464PiPairs.getD k (0,0))
    (sourceEtaBatch6464Lower k, sourceEtaBatch6464Upper k)
    (sourceBlock6464TwoPairs.getD k (0,0))

theorem sourceBlock6464Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6464XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6464+k):ℂ)).re ∧
      (xi (xiGridArgument (6464+k):ℂ)).re ≤ ((sourceBlock6464XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6464+k) _ _ _
    (sourceBlock6464PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6464_actual_enclosure k hk)
    (sourceBlock6464TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6464Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6464XiPair k).1 := by
  decide +kernel

theorem sourceBlock6464Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6464Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6464XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6464XiPair k)).2 ≤
      sourceBlock6464Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6464_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6464+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6464+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6464Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6464+k) (sourceBlock6464XiPair k) _
    (sourceBlock6464Xi_enclosure k hk) (sourceBlock6464Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6464Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6496_bound (k : ℕ) (hk : k < 6496) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6464
  · exact sourceRoundedMidpoint_first6464_bound k h
  · have hsum : 6464+(k-6464) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6464_bound (k-6464) (by omega)

end ReciprocalXi
