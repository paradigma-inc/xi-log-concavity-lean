import ProofWorkspace.Final.SourceBlock4768Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4800DataFull
import ProofWorkspace.Final.EtaBlock4800Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4800XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4800+k) (sourceBlock4800PiPairs.getD k (0,0))
    (sourceEtaBatch4800Lower k, sourceEtaBatch4800Upper k)
    (sourceBlock4800TwoPairs.getD k (0,0))

theorem sourceBlock4800Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4800XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4800+k):ℂ)).re ∧
      (xi (xiGridArgument (4800+k):ℂ)).re ≤ ((sourceBlock4800XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4800+k) _ _ _
    (sourceBlock4800PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4800_actual_enclosure k hk)
    (sourceBlock4800TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4800Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4800XiPair k).1 := by
  decide +kernel

theorem sourceBlock4800Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4800Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4800XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4800XiPair k)).2 ≤
      sourceBlock4800Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4800_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4800+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4800+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4800Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4800+k) (sourceBlock4800XiPair k) _
    (sourceBlock4800Xi_enclosure k hk) (sourceBlock4800Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4800Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4832_bound (k : ℕ) (hk : k < 4832) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4800
  · exact sourceRoundedMidpoint_first4800_bound k h
  · have hsum : 4800+(k-4800) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4800_bound (k-4800) (by omega)

end ReciprocalXi
