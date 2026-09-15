import ProofWorkspace.Final.SourceBlock9600Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9632DataFull
import ProofWorkspace.Final.EtaBlock9632Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9632XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9632+k) (sourceBlock9632PiPairs.getD k (0,0))
    (sourceEtaBatch9632Lower k, sourceEtaBatch9632Upper k)
    (sourceBlock9632TwoPairs.getD k (0,0))

theorem sourceBlock9632Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9632XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9632+k):ℂ)).re ∧
      (xi (xiGridArgument (9632+k):ℂ)).re ≤ ((sourceBlock9632XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9632+k) _ _ _
    (sourceBlock9632PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9632_actual_enclosure k hk)
    (sourceBlock9632TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9632Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9632XiPair k).1 := by
  decide +kernel

theorem sourceBlock9632Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9632Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9632XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9632XiPair k)).2 ≤
      sourceBlock9632Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9632_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9632+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9632+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9632Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9632+k) (sourceBlock9632XiPair k) _
    (sourceBlock9632Xi_enclosure k hk) (sourceBlock9632Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9632Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9664_bound (k : ℕ) (hk : k < 9664) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9632
  · exact sourceRoundedMidpoint_first9632_bound k h
  · have hsum : 9632+(k-9632) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9632_bound (k-9632) (by omega)

end ReciprocalXi
