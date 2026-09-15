import ProofWorkspace.Final.SourceBlock10912Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10944DataFull
import ProofWorkspace.Final.EtaBlock10944Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10944XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10944+k) (sourceBlock10944PiPairs.getD k (0,0))
    (sourceEtaBatch10944Lower k, sourceEtaBatch10944Upper k)
    (sourceBlock10944TwoPairs.getD k (0,0))

theorem sourceBlock10944Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10944XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10944+k):ℂ)).re ∧
      (xi (xiGridArgument (10944+k):ℂ)).re ≤ ((sourceBlock10944XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10944+k) _ _ _
    (sourceBlock10944PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10944_actual_enclosure k hk)
    (sourceBlock10944TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10944Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10944XiPair k).1 := by
  decide +kernel

theorem sourceBlock10944Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10944Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10944XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10944XiPair k)).2 ≤
      sourceBlock10944Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10944_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10944+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10944+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10944Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10944+k) (sourceBlock10944XiPair k) _
    (sourceBlock10944Xi_enclosure k hk) (sourceBlock10944Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10944Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10976_bound (k : ℕ) (hk : k < 10976) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10944
  · exact sourceRoundedMidpoint_first10944_bound k h
  · have hsum : 10944+(k-10944) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10944_bound (k-10944) (by omega)

end ReciprocalXi
