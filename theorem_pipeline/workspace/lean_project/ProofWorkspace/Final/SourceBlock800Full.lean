import ProofWorkspace.Final.SourceBlock768Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock800DataFull
import ProofWorkspace.Final.EtaBlock800Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock800XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (800+k) (sourceBlock800PiPairs.getD k (0,0))
    (sourceEtaBatch800Lower k, sourceEtaBatch800Upper k)
    (sourceBlock800TwoPairs.getD k (0,0))

theorem sourceBlock800Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock800XiPair k).1:ℝ) ≤ (xi (xiGridArgument (800+k):ℂ)).re ∧
      (xi (xiGridArgument (800+k):ℂ)).re ≤ ((sourceBlock800XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (800+k) _ _ _
    (sourceBlock800PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch800_actual_enclosure k hk)
    (sourceBlock800TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock800Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock800XiPair k).1 := by
  decide +kernel

theorem sourceBlock800Reciprocal_check : ∀ k : Fin 32,
    sourceBlock800Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock800XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock800XiPair k)).2 ≤
      sourceBlock800Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block800_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((800+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (800+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock800Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (800+k) (sourceBlock800XiPair k) _
    (sourceBlock800Xi_enclosure k hk) (sourceBlock800Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock800Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first832_bound (k : ℕ) (hk : k < 832) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 800
  · exact sourceRoundedMidpoint_first800_bound k h
  · have hsum : 800+(k-800) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block800_bound (k-800) (by omega)

end ReciprocalXi
