import ProofWorkspace.Final.SourceBlock480Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock512DataFull
import ProofWorkspace.Final.EtaBlock512Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock512XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (512+k) (sourceBlock512PiPairs.getD k (0,0))
    (sourceEtaBatch512Lower k, sourceEtaBatch512Upper k)
    (sourceBlock512TwoPairs.getD k (0,0))

theorem sourceBlock512Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock512XiPair k).1:ℝ) ≤ (xi (xiGridArgument (512+k):ℂ)).re ∧
      (xi (xiGridArgument (512+k):ℂ)).re ≤ ((sourceBlock512XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (512+k) _ _ _
    (sourceBlock512PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch512_actual_enclosure k hk)
    (sourceBlock512TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock512Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock512XiPair k).1 := by
  decide +kernel

theorem sourceBlock512Reciprocal_check : ∀ k : Fin 32,
    sourceBlock512Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock512XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock512XiPair k)).2 ≤
      sourceBlock512Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block512_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((512+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (512+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock512Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (512+k) (sourceBlock512XiPair k) _
    (sourceBlock512Xi_enclosure k hk) (sourceBlock512Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock512Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first544_bound (k : ℕ) (hk : k < 544) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 512
  · exact sourceRoundedMidpoint_first512_bound k h
  · have hsum : 512+(k-512) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block512_bound (k-512) (by omega)

end ReciprocalXi
