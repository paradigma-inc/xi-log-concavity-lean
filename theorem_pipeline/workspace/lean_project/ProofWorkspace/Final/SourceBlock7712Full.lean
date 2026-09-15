import ProofWorkspace.Final.SourceBlock7680Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock7712DataFull
import ProofWorkspace.Final.EtaBlock7712Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock7712XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (7712+k) (sourceBlock7712PiPairs.getD k (0,0))
    (sourceEtaBatch7712Lower k, sourceEtaBatch7712Upper k)
    (sourceBlock7712TwoPairs.getD k (0,0))

theorem sourceBlock7712Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock7712XiPair k).1:ℝ) ≤ (xi (xiGridArgument (7712+k):ℂ)).re ∧
      (xi (xiGridArgument (7712+k):ℂ)).re ≤ ((sourceBlock7712XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (7712+k) _ _ _
    (sourceBlock7712PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch7712_actual_enclosure k hk)
    (sourceBlock7712TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock7712Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock7712XiPair k).1 := by
  decide +kernel

theorem sourceBlock7712Reciprocal_check : ∀ k : Fin 32,
    sourceBlock7712Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock7712XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock7712XiPair k)).2 ≤
      sourceBlock7712Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block7712_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((7712+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (7712+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock7712Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (7712+k) (sourceBlock7712XiPair k) _
    (sourceBlock7712Xi_enclosure k hk) (sourceBlock7712Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock7712Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first7744_bound (k : ℕ) (hk : k < 7744) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 7712
  · exact sourceRoundedMidpoint_first7712_bound k h
  · have hsum : 7712+(k-7712) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block7712_bound (k-7712) (by omega)

end ReciprocalXi
