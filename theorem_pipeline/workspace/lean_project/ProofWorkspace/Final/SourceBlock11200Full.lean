import ProofWorkspace.Final.SourceBlock11168Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11200DataFull
import ProofWorkspace.Final.EtaBlock11200Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11200XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11200+k) (sourceBlock11200PiPairs.getD k (0,0))
    (sourceEtaBatch11200Lower k, sourceEtaBatch11200Upper k)
    (sourceBlock11200TwoPairs.getD k (0,0))

theorem sourceBlock11200Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11200XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11200+k):ℂ)).re ∧
      (xi (xiGridArgument (11200+k):ℂ)).re ≤ ((sourceBlock11200XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11200+k) _ _ _
    (sourceBlock11200PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11200_actual_enclosure k hk)
    (sourceBlock11200TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11200Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11200XiPair k).1 := by
  decide +kernel

theorem sourceBlock11200Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11200Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11200XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11200XiPair k)).2 ≤
      sourceBlock11200Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11200_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11200+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11200+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11200Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11200+k) (sourceBlock11200XiPair k) _
    (sourceBlock11200Xi_enclosure k hk) (sourceBlock11200Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11200Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11232_bound (k : ℕ) (hk : k < 11232) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11200
  · exact sourceRoundedMidpoint_first11200_bound k h
  · have hsum : 11200+(k-11200) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11200_bound (k-11200) (by omega)

end ReciprocalXi
