import ProofWorkspace.Final.SourceBlock10816Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10848DataFull
import ProofWorkspace.Final.EtaBlock10848Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10848XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10848+k) (sourceBlock10848PiPairs.getD k (0,0))
    (sourceEtaBatch10848Lower k, sourceEtaBatch10848Upper k)
    (sourceBlock10848TwoPairs.getD k (0,0))

theorem sourceBlock10848Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10848XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10848+k):ℂ)).re ∧
      (xi (xiGridArgument (10848+k):ℂ)).re ≤ ((sourceBlock10848XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10848+k) _ _ _
    (sourceBlock10848PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10848_actual_enclosure k hk)
    (sourceBlock10848TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10848Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10848XiPair k).1 := by
  decide +kernel

theorem sourceBlock10848Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10848Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10848XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10848XiPair k)).2 ≤
      sourceBlock10848Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10848_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10848+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10848+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10848Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10848+k) (sourceBlock10848XiPair k) _
    (sourceBlock10848Xi_enclosure k hk) (sourceBlock10848Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10848Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10880_bound (k : ℕ) (hk : k < 10880) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10848
  · exact sourceRoundedMidpoint_first10848_bound k h
  · have hsum : 10848+(k-10848) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10848_bound (k-10848) (by omega)

end ReciprocalXi
