import ProofWorkspace.Final.SourceBlock13312Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock13344DataFull
import ProofWorkspace.Final.EtaBlock13344Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock13344XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (13344+k) (sourceBlock13344PiPairs.getD k (0,0))
    (sourceEtaBatch13344Lower k, sourceEtaBatch13344Upper k)
    (sourceBlock13344TwoPairs.getD k (0,0))

theorem sourceBlock13344Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock13344XiPair k).1:ℝ) ≤ (xi (xiGridArgument (13344+k):ℂ)).re ∧
      (xi (xiGridArgument (13344+k):ℂ)).re ≤ ((sourceBlock13344XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (13344+k) _ _ _
    (sourceBlock13344PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch13344_actual_enclosure k hk)
    (sourceBlock13344TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock13344Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock13344XiPair k).1 := by
  decide +kernel

theorem sourceBlock13344Reciprocal_check : ∀ k : Fin 32,
    sourceBlock13344Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock13344XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock13344XiPair k)).2 ≤
      sourceBlock13344Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block13344_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((13344+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (13344+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock13344Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (13344+k) (sourceBlock13344XiPair k) _
    (sourceBlock13344Xi_enclosure k hk) (sourceBlock13344Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock13344Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first13376_bound (k : ℕ) (hk : k < 13376) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 13344
  · exact sourceRoundedMidpoint_first13344_bound k h
  · have hsum : 13344+(k-13344) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block13344_bound (k-13344) (by omega)

end ReciprocalXi
