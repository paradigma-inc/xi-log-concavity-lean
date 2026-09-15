import ProofWorkspace.Final.SourceBlock9152Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9184DataFull
import ProofWorkspace.Final.EtaBlock9184Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9184XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9184+k) (sourceBlock9184PiPairs.getD k (0,0))
    (sourceEtaBatch9184Lower k, sourceEtaBatch9184Upper k)
    (sourceBlock9184TwoPairs.getD k (0,0))

theorem sourceBlock9184Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9184XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9184+k):ℂ)).re ∧
      (xi (xiGridArgument (9184+k):ℂ)).re ≤ ((sourceBlock9184XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9184+k) _ _ _
    (sourceBlock9184PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9184_actual_enclosure k hk)
    (sourceBlock9184TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9184Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9184XiPair k).1 := by
  decide +kernel

theorem sourceBlock9184Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9184Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9184XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9184XiPair k)).2 ≤
      sourceBlock9184Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9184_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9184+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9184+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9184Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9184+k) (sourceBlock9184XiPair k) _
    (sourceBlock9184Xi_enclosure k hk) (sourceBlock9184Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9184Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9216_bound (k : ℕ) (hk : k < 9216) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9184
  · exact sourceRoundedMidpoint_first9184_bound k h
  · have hsum : 9184+(k-9184) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9184_bound (k-9184) (by omega)

end ReciprocalXi
