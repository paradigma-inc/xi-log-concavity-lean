import ProofWorkspace.Final.SourceBlock6528Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6560DataFull
import ProofWorkspace.Final.EtaBlock6560Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6560XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6560+k) (sourceBlock6560PiPairs.getD k (0,0))
    (sourceEtaBatch6560Lower k, sourceEtaBatch6560Upper k)
    (sourceBlock6560TwoPairs.getD k (0,0))

theorem sourceBlock6560Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6560XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6560+k):ℂ)).re ∧
      (xi (xiGridArgument (6560+k):ℂ)).re ≤ ((sourceBlock6560XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6560+k) _ _ _
    (sourceBlock6560PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6560_actual_enclosure k hk)
    (sourceBlock6560TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6560Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6560XiPair k).1 := by
  decide +kernel

theorem sourceBlock6560Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6560Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6560XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6560XiPair k)).2 ≤
      sourceBlock6560Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6560_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6560+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6560+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6560Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6560+k) (sourceBlock6560XiPair k) _
    (sourceBlock6560Xi_enclosure k hk) (sourceBlock6560Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6560Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6592_bound (k : ℕ) (hk : k < 6592) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6560
  · exact sourceRoundedMidpoint_first6560_bound k h
  · have hsum : 6560+(k-6560) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6560_bound (k-6560) (by omega)

end ReciprocalXi
