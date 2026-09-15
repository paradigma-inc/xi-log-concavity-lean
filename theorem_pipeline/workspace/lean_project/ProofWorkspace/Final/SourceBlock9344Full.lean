import ProofWorkspace.Final.SourceBlock9312Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock9344DataFull
import ProofWorkspace.Final.EtaBlock9344Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock9344XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (9344+k) (sourceBlock9344PiPairs.getD k (0,0))
    (sourceEtaBatch9344Lower k, sourceEtaBatch9344Upper k)
    (sourceBlock9344TwoPairs.getD k (0,0))

theorem sourceBlock9344Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock9344XiPair k).1:ℝ) ≤ (xi (xiGridArgument (9344+k):ℂ)).re ∧
      (xi (xiGridArgument (9344+k):ℂ)).re ≤ ((sourceBlock9344XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (9344+k) _ _ _
    (sourceBlock9344PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch9344_actual_enclosure k hk)
    (sourceBlock9344TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock9344Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock9344XiPair k).1 := by
  decide +kernel

theorem sourceBlock9344Reciprocal_check : ∀ k : Fin 32,
    sourceBlock9344Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock9344XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock9344XiPair k)).2 ≤
      sourceBlock9344Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block9344_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((9344+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (9344+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock9344Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (9344+k) (sourceBlock9344XiPair k) _
    (sourceBlock9344Xi_enclosure k hk) (sourceBlock9344Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock9344Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9376_bound (k : ℕ) (hk : k < 9376) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 9344
  · exact sourceRoundedMidpoint_first9344_bound k h
  · have hsum : 9344+(k-9344) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block9344_bound (k-9344) (by omega)

end ReciprocalXi
