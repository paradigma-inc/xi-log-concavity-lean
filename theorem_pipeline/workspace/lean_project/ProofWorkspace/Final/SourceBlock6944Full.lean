import ProofWorkspace.Final.SourceBlock6912Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock6944DataFull
import ProofWorkspace.Final.EtaBlock6944Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock6944XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (6944+k) (sourceBlock6944PiPairs.getD k (0,0))
    (sourceEtaBatch6944Lower k, sourceEtaBatch6944Upper k)
    (sourceBlock6944TwoPairs.getD k (0,0))

theorem sourceBlock6944Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock6944XiPair k).1:ℝ) ≤ (xi (xiGridArgument (6944+k):ℂ)).re ∧
      (xi (xiGridArgument (6944+k):ℂ)).re ≤ ((sourceBlock6944XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (6944+k) _ _ _
    (sourceBlock6944PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch6944_actual_enclosure k hk)
    (sourceBlock6944TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock6944Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock6944XiPair k).1 := by
  decide +kernel

theorem sourceBlock6944Reciprocal_check : ∀ k : Fin 32,
    sourceBlock6944Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock6944XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock6944XiPair k)).2 ≤
      sourceBlock6944Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block6944_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((6944+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (6944+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock6944Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (6944+k) (sourceBlock6944XiPair k) _
    (sourceBlock6944Xi_enclosure k hk) (sourceBlock6944Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock6944Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first6976_bound (k : ℕ) (hk : k < 6976) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 6944
  · exact sourceRoundedMidpoint_first6944_bound k h
  · have hsum : 6944+(k-6944) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block6944_bound (k-6944) (by omega)

end ReciprocalXi
