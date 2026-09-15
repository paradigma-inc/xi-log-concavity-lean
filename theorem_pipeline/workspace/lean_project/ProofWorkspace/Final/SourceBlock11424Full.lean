import ProofWorkspace.Final.SourceBlock11392Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11424DataFull
import ProofWorkspace.Final.EtaBlock11424Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11424XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11424+k) (sourceBlock11424PiPairs.getD k (0,0))
    (sourceEtaBatch11424Lower k, sourceEtaBatch11424Upper k)
    (sourceBlock11424TwoPairs.getD k (0,0))

theorem sourceBlock11424Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11424XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11424+k):ℂ)).re ∧
      (xi (xiGridArgument (11424+k):ℂ)).re ≤ ((sourceBlock11424XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11424+k) _ _ _
    (sourceBlock11424PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11424_actual_enclosure k hk)
    (sourceBlock11424TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11424Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11424XiPair k).1 := by
  decide +kernel

theorem sourceBlock11424Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11424Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11424XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11424XiPair k)).2 ≤
      sourceBlock11424Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11424_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11424+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11424+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11424Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11424+k) (sourceBlock11424XiPair k) _
    (sourceBlock11424Xi_enclosure k hk) (sourceBlock11424Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11424Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11456_bound (k : ℕ) (hk : k < 11456) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11424
  · exact sourceRoundedMidpoint_first11424_bound k h
  · have hsum : 11424+(k-11424) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11424_bound (k-11424) (by omega)

end ReciprocalXi
