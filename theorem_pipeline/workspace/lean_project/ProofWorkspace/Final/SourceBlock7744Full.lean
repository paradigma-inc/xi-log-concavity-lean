import ProofWorkspace.Final.SourceBlock7712Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7744DataFull
import ProofWorkspace.Final.EtaBlock7744Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7744XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7744+k) (sourceBlock7744PiPairs.getD k (0,0))
    (sourceEtaBatch7744Lower k, sourceEtaBatch7744Upper k)
    (sourceBlock7744TwoPairs.getD k (0,0))

theorem sourceBlock7744Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7744XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7744+k):ℂ)).re ∧
      (xi (xiGridArgument (7744+k):ℂ)).re ≤ ((sourceBlock7744XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7744+k) _ _ _
    (sourceBlock7744PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7744_actual_enclosure k hk)
    (sourceBlock7744TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7744Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7744XiPair k).1 := by
  decide +kernel

theorem sourceBlock7744Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7744Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7744XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7744XiPair k)).2 ≤
      sourceBlock7744Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7744_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7744+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7744+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7744Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7744+k) (sourceBlock7744XiPair k) _
    (sourceBlock7744Xi_enclosure k hk) (sourceBlock7744Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7744Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7776_bound (k : ℕ) (hk : k < 7776) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7744
  · exact sourceRoundedMidpoint_first7744_bound k h
  · have hsum : 7744+(k-7744) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7744_bound (k-7744) (by omega)

end ReciprocalXi
