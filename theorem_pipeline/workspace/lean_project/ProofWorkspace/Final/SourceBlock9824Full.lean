import ProofWorkspace.Final.SourceBlock9792Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9824DataFull
import ProofWorkspace.Final.EtaBlock9824Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9824XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9824+k) (sourceBlock9824PiPairs.getD k (0,0))
    (sourceEtaBatch9824Lower k, sourceEtaBatch9824Upper k)
    (sourceBlock9824TwoPairs.getD k (0,0))

theorem sourceBlock9824Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9824XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9824+k):ℂ)).re ∧
      (xi (xiGridArgument (9824+k):ℂ)).re ≤ ((sourceBlock9824XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9824+k) _ _ _
    (sourceBlock9824PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9824_actual_enclosure k hk)
    (sourceBlock9824TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9824Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9824XiPair k).1 := by
  decide +kernel

theorem sourceBlock9824Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9824Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9824XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9824XiPair k)).2 ≤
      sourceBlock9824Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9824_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9824+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9824+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9824Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9824+k) (sourceBlock9824XiPair k) _
    (sourceBlock9824Xi_enclosure k hk) (sourceBlock9824Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9824Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9856_bound (k : ℕ) (hk : k < 9856) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9824
  · exact sourceRoundedMidpoint_first9824_bound k h
  · have hsum : 9824+(k-9824) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9824_bound (k-9824) (by omega)

end ReciprocalXi
