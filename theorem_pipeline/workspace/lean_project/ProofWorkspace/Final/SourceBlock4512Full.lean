import ProofWorkspace.Final.SourceBlock4480Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock4512DataFull
import ProofWorkspace.Final.EtaBlock4512Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock4512XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (4512+k) (sourceBlock4512PiPairs.getD k (0,0))
    (sourceEtaBatch4512Lower k, sourceEtaBatch4512Upper k)
    (sourceBlock4512TwoPairs.getD k (0,0))

theorem sourceBlock4512Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock4512XiPair k).1:ℝ) ≤ (xi (xiGridArgument (4512+k):ℂ)).re ∧
      (xi (xiGridArgument (4512+k):ℂ)).re ≤ ((sourceBlock4512XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (4512+k) _ _ _
    (sourceBlock4512PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch4512_actual_enclosure k hk)
    (sourceBlock4512TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock4512Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock4512XiPair k).1 := by
  decide +kernel

theorem sourceBlock4512Reciprocal_check : ∀ k : Fin 32,
    sourceBlock4512Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock4512XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock4512XiPair k)).2 ≤
      sourceBlock4512Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block4512_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((4512+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (4512+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock4512Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (4512+k) (sourceBlock4512XiPair k) _
    (sourceBlock4512Xi_enclosure k hk) (sourceBlock4512Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock4512Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first4544_bound (k : ℕ) (hk : k < 4544) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 4512
  · exact sourceRoundedMidpoint_first4512_bound k h
  · have hsum : 4512+(k-4512) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block4512_bound (k-4512) (by omega)

end ReciprocalXi
