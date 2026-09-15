import ProofWorkspace.Final.SourceBlock6624Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6656DataFull
import ProofWorkspace.Final.EtaBlock6656Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6656XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6656+k) (sourceBlock6656PiPairs.getD k (0,0))
    (sourceEtaBatch6656Lower k, sourceEtaBatch6656Upper k)
    (sourceBlock6656TwoPairs.getD k (0,0))

theorem sourceBlock6656Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6656XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6656+k):ℂ)).re ∧
      (xi (xiGridArgument (6656+k):ℂ)).re ≤ ((sourceBlock6656XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6656+k) _ _ _
    (sourceBlock6656PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6656_actual_enclosure k hk)
    (sourceBlock6656TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6656Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6656XiPair k).1 := by
  decide +kernel

theorem sourceBlock6656Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6656Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6656XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6656XiPair k)).2 ≤
      sourceBlock6656Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6656_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6656+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6656+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6656Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6656+k) (sourceBlock6656XiPair k) _
    (sourceBlock6656Xi_enclosure k hk) (sourceBlock6656Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6656Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6688_bound (k : ℕ) (hk : k < 6688) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6656
  · exact sourceRoundedMidpoint_first6656_bound k h
  · have hsum : 6656+(k-6656) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6656_bound (k-6656) (by omega)

end ReciprocalXi
