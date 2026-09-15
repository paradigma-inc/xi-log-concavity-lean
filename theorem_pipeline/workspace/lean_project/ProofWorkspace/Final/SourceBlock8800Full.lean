import ProofWorkspace.Final.SourceBlock8768Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8800DataFull
import ProofWorkspace.Final.EtaBlock8800Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8800XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8800+k) (sourceBlock8800PiPairs.getD k (0,0))
    (sourceEtaBatch8800Lower k, sourceEtaBatch8800Upper k)
    (sourceBlock8800TwoPairs.getD k (0,0))

theorem sourceBlock8800Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8800XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8800+k):ℂ)).re ∧
      (xi (xiGridArgument (8800+k):ℂ)).re ≤ ((sourceBlock8800XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8800+k) _ _ _
    (sourceBlock8800PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8800_actual_enclosure k hk)
    (sourceBlock8800TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8800Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8800XiPair k).1 := by
  decide +kernel

theorem sourceBlock8800Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8800Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8800XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8800XiPair k)).2 ≤
      sourceBlock8800Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8800_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8800+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8800+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8800Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8800+k) (sourceBlock8800XiPair k) _
    (sourceBlock8800Xi_enclosure k hk) (sourceBlock8800Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8800Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8832_bound (k : ℕ) (hk : k < 8832) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8800
  · exact sourceRoundedMidpoint_first8800_bound k h
  · have hsum : 8800+(k-8800) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8800_bound (k-8800) (by omega)

end ReciprocalXi
