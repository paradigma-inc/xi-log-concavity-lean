import ProofWorkspace.Final.SourceBlock13344Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13376DataFull
import ProofWorkspace.Final.EtaBlock13376Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13376XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13376+k) (sourceBlock13376PiPairs.getD k (0,0))
    (sourceEtaBatch13376Lower k, sourceEtaBatch13376Upper k)
    (sourceBlock13376TwoPairs.getD k (0,0))

theorem sourceBlock13376Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13376XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13376+k):ℂ)).re ∧
      (xi (xiGridArgument (13376+k):ℂ)).re ≤ ((sourceBlock13376XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13376+k) _ _ _
    (sourceBlock13376PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13376_actual_enclosure k hk)
    (sourceBlock13376TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13376Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13376XiPair k).1 := by
  decide +kernel

theorem sourceBlock13376Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13376Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13376XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13376XiPair k)).2 ≤
      sourceBlock13376Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13376_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13376+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13376+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13376Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13376+k) (sourceBlock13376XiPair k) _
    (sourceBlock13376Xi_enclosure k hk) (sourceBlock13376Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13376Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13408_bound (k : ℕ) (hk : k < 13408) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13376
  · exact sourceRoundedMidpoint_first13376_bound k h
  · have hsum : 13376+(k-13376) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13376_bound (k-13376) (by omega)

end ReciprocalXi
