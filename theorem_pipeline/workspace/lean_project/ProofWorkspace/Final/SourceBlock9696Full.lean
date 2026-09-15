import ProofWorkspace.Final.SourceBlock9664Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9696DataFull
import ProofWorkspace.Final.EtaBlock9696Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9696XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9696+k) (sourceBlock9696PiPairs.getD k (0,0))
    (sourceEtaBatch9696Lower k, sourceEtaBatch9696Upper k)
    (sourceBlock9696TwoPairs.getD k (0,0))

theorem sourceBlock9696Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9696XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9696+k):ℂ)).re ∧
      (xi (xiGridArgument (9696+k):ℂ)).re ≤ ((sourceBlock9696XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9696+k) _ _ _
    (sourceBlock9696PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9696_actual_enclosure k hk)
    (sourceBlock9696TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9696Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9696XiPair k).1 := by
  decide +kernel

theorem sourceBlock9696Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9696Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9696XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9696XiPair k)).2 ≤
      sourceBlock9696Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9696_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9696+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9696+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9696Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9696+k) (sourceBlock9696XiPair k) _
    (sourceBlock9696Xi_enclosure k hk) (sourceBlock9696Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9696Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9728_bound (k : ℕ) (hk : k < 9728) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9696
  · exact sourceRoundedMidpoint_first9696_bound k h
  · have hsum : 9696+(k-9696) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9696_bound (k-9696) (by omega)

end ReciprocalXi
