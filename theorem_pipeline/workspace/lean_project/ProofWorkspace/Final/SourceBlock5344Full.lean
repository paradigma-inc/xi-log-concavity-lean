import ProofWorkspace.Final.SourceBlock5312Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5344DataFull
import ProofWorkspace.Final.EtaBlock5344Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5344XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5344+k) (sourceBlock5344PiPairs.getD k (0,0))
    (sourceEtaBatch5344Lower k, sourceEtaBatch5344Upper k)
    (sourceBlock5344TwoPairs.getD k (0,0))

theorem sourceBlock5344Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5344XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5344+k):ℂ)).re ∧
      (xi (xiGridArgument (5344+k):ℂ)).re ≤ ((sourceBlock5344XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5344+k) _ _ _
    (sourceBlock5344PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5344_actual_enclosure k hk)
    (sourceBlock5344TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5344Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5344XiPair k).1 := by
  decide +kernel

theorem sourceBlock5344Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5344Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5344XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5344XiPair k)).2 ≤
      sourceBlock5344Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5344_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5344+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5344+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5344Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5344+k) (sourceBlock5344XiPair k) _
    (sourceBlock5344Xi_enclosure k hk) (sourceBlock5344Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5344Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5376_bound (k : ℕ) (hk : k < 5376) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5344
  · exact sourceRoundedMidpoint_first5344_bound k h
  · have hsum : 5344+(k-5344) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5344_bound (k-5344) (by omega)

end ReciprocalXi
