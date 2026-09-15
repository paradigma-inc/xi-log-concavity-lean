import ProofWorkspace.Final.SourceBlock8992Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9024DataFull
import ProofWorkspace.Final.EtaBlock9024Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9024XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9024+k) (sourceBlock9024PiPairs.getD k (0,0))
    (sourceEtaBatch9024Lower k, sourceEtaBatch9024Upper k)
    (sourceBlock9024TwoPairs.getD k (0,0))

theorem sourceBlock9024Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9024XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9024+k):ℂ)).re ∧
      (xi (xiGridArgument (9024+k):ℂ)).re ≤ ((sourceBlock9024XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9024+k) _ _ _
    (sourceBlock9024PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9024_actual_enclosure k hk)
    (sourceBlock9024TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9024Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9024XiPair k).1 := by
  decide +kernel

theorem sourceBlock9024Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9024Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9024XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9024XiPair k)).2 ≤
      sourceBlock9024Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9024_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9024+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9024+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9024Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9024+k) (sourceBlock9024XiPair k) _
    (sourceBlock9024Xi_enclosure k hk) (sourceBlock9024Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9024Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9056_bound (k : ℕ) (hk : k < 9056) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9024
  · exact sourceRoundedMidpoint_first9024_bound k h
  · have hsum : 9024+(k-9024) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9024_bound (k-9024) (by omega)

end ReciprocalXi
