import ProofWorkspace.Final.SourceBlock7584Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7616DataFull
import ProofWorkspace.Final.EtaBlock7616Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7616XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7616+k) (sourceBlock7616PiPairs.getD k (0,0))
    (sourceEtaBatch7616Lower k, sourceEtaBatch7616Upper k)
    (sourceBlock7616TwoPairs.getD k (0,0))

theorem sourceBlock7616Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7616XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7616+k):ℂ)).re ∧
      (xi (xiGridArgument (7616+k):ℂ)).re ≤ ((sourceBlock7616XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7616+k) _ _ _
    (sourceBlock7616PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7616_actual_enclosure k hk)
    (sourceBlock7616TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7616Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7616XiPair k).1 := by
  decide +kernel

theorem sourceBlock7616Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7616Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7616XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7616XiPair k)).2 ≤
      sourceBlock7616Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7616_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7616+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7616+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7616Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7616+k) (sourceBlock7616XiPair k) _
    (sourceBlock7616Xi_enclosure k hk) (sourceBlock7616Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7616Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7648_bound (k : ℕ) (hk : k < 7648) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7616
  · exact sourceRoundedMidpoint_first7616_bound k h
  · have hsum : 7616+(k-7616) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7616_bound (k-7616) (by omega)

end ReciprocalXi
