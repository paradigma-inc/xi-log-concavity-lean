import ProofWorkspace.Final.SourceBlock6144Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6176DataFull
import ProofWorkspace.Final.EtaBlock6176Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6176XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6176+k) (sourceBlock6176PiPairs.getD k (0,0))
    (sourceEtaBatch6176Lower k, sourceEtaBatch6176Upper k)
    (sourceBlock6176TwoPairs.getD k (0,0))

theorem sourceBlock6176Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6176XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6176+k):ℂ)).re ∧
      (xi (xiGridArgument (6176+k):ℂ)).re ≤ ((sourceBlock6176XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6176+k) _ _ _
    (sourceBlock6176PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6176_actual_enclosure k hk)
    (sourceBlock6176TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6176Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6176XiPair k).1 := by
  decide +kernel

theorem sourceBlock6176Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6176Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6176XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6176XiPair k)).2 ≤
      sourceBlock6176Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6176_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6176+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6176+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6176Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6176+k) (sourceBlock6176XiPair k) _
    (sourceBlock6176Xi_enclosure k hk) (sourceBlock6176Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6176Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6208_bound (k : ℕ) (hk : k < 6208) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6176
  · exact sourceRoundedMidpoint_first6176_bound k h
  · have hsum : 6176+(k-6176) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6176_bound (k-6176) (by omega)

end ReciprocalXi
