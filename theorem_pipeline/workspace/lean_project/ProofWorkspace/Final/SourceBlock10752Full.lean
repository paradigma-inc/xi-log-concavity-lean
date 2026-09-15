import ProofWorkspace.Final.SourceBlock10720Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10752DataFull
import ProofWorkspace.Final.EtaBlock10752Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10752XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10752+k) (sourceBlock10752PiPairs.getD k (0,0))
    (sourceEtaBatch10752Lower k, sourceEtaBatch10752Upper k)
    (sourceBlock10752TwoPairs.getD k (0,0))

theorem sourceBlock10752Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10752XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10752+k):ℂ)).re ∧
      (xi (xiGridArgument (10752+k):ℂ)).re ≤ ((sourceBlock10752XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10752+k) _ _ _
    (sourceBlock10752PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10752_actual_enclosure k hk)
    (sourceBlock10752TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10752Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10752XiPair k).1 := by
  decide +kernel

theorem sourceBlock10752Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10752Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10752XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10752XiPair k)).2 ≤
      sourceBlock10752Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10752_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10752+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10752+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10752Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10752+k) (sourceBlock10752XiPair k) _
    (sourceBlock10752Xi_enclosure k hk) (sourceBlock10752Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10752Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10784_bound (k : ℕ) (hk : k < 10784) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10752
  · exact sourceRoundedMidpoint_first10752_bound k h
  · have hsum : 10752+(k-10752) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10752_bound (k-10752) (by omega)

end ReciprocalXi
