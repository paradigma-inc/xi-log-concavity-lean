import ProofWorkspace.Final.SourceBlock5344Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5376DataFull
import ProofWorkspace.Final.EtaBlock5376Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5376XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5376+k) (sourceBlock5376PiPairs.getD k (0,0))
    (sourceEtaBatch5376Lower k, sourceEtaBatch5376Upper k)
    (sourceBlock5376TwoPairs.getD k (0,0))

theorem sourceBlock5376Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5376XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5376+k):ℂ)).re ∧
      (xi (xiGridArgument (5376+k):ℂ)).re ≤ ((sourceBlock5376XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5376+k) _ _ _
    (sourceBlock5376PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5376_actual_enclosure k hk)
    (sourceBlock5376TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5376Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5376XiPair k).1 := by
  decide +kernel

theorem sourceBlock5376Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5376Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5376XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5376XiPair k)).2 ≤
      sourceBlock5376Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5376_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5376+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5376+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5376Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5376+k) (sourceBlock5376XiPair k) _
    (sourceBlock5376Xi_enclosure k hk) (sourceBlock5376Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5376Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5408_bound (k : ℕ) (hk : k < 5408) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5376
  · exact sourceRoundedMidpoint_first5376_bound k h
  · have hsum : 5376+(k-5376) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5376_bound (k-5376) (by omega)

end ReciprocalXi
