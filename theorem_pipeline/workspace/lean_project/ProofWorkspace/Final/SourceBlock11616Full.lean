import ProofWorkspace.Final.SourceBlock11584Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11616DataFull
import ProofWorkspace.Final.EtaBlock11616Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11616XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11616+k) (sourceBlock11616PiPairs.getD k (0,0))
    (sourceEtaBatch11616Lower k, sourceEtaBatch11616Upper k)
    (sourceBlock11616TwoPairs.getD k (0,0))

theorem sourceBlock11616Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11616XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11616+k):ℂ)).re ∧
      (xi (xiGridArgument (11616+k):ℂ)).re ≤ ((sourceBlock11616XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11616+k) _ _ _
    (sourceBlock11616PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11616_actual_enclosure k hk)
    (sourceBlock11616TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11616Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11616XiPair k).1 := by
  decide +kernel

theorem sourceBlock11616Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11616Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11616XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11616XiPair k)).2 ≤
      sourceBlock11616Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11616_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11616+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11616+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11616Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11616+k) (sourceBlock11616XiPair k) _
    (sourceBlock11616Xi_enclosure k hk) (sourceBlock11616Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11616Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11648_bound (k : ℕ) (hk : k < 11648) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11616
  · exact sourceRoundedMidpoint_first11616_bound k h
  · have hsum : 11616+(k-11616) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11616_bound (k-11616) (by omega)

end ReciprocalXi
