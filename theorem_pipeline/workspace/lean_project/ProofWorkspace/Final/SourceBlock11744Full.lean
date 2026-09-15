import ProofWorkspace.Final.SourceBlock11712Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock11744DataFull
import ProofWorkspace.Final.EtaBlock11744Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock11744XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (11744+k) (sourceBlock11744PiPairs.getD k (0,0))
    (sourceEtaBatch11744Lower k, sourceEtaBatch11744Upper k)
    (sourceBlock11744TwoPairs.getD k (0,0))

theorem sourceBlock11744Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock11744XiPair k).1:ℝ) ≤ (xi (xiGridArgument (11744+k):ℂ)).re ∧
      (xi (xiGridArgument (11744+k):ℂ)).re ≤ ((sourceBlock11744XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (11744+k) _ _ _
    (sourceBlock11744PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch11744_actual_enclosure k hk)
    (sourceBlock11744TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock11744Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock11744XiPair k).1 := by
  decide +kernel

theorem sourceBlock11744Reciprocal_check : ∀ k : Fin 32,
    sourceBlock11744Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock11744XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock11744XiPair k)).2 ≤
      sourceBlock11744Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block11744_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((11744+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (11744+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock11744Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (11744+k) (sourceBlock11744XiPair k) _
    (sourceBlock11744Xi_enclosure k hk) (sourceBlock11744Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock11744Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first11776_bound (k : ℕ) (hk : k < 11776) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 11744
  · exact sourceRoundedMidpoint_first11744_bound k h
  · have hsum : 11744+(k-11744) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block11744_bound (k-11744) (by omega)

end ReciprocalXi
