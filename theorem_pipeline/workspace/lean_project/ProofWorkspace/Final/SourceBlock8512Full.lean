import ProofWorkspace.Final.SourceBlock8480Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8512DataFull
import ProofWorkspace.Final.EtaBlock8512Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8512XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8512+k) (sourceBlock8512PiPairs.getD k (0,0))
    (sourceEtaBatch8512Lower k, sourceEtaBatch8512Upper k)
    (sourceBlock8512TwoPairs.getD k (0,0))

theorem sourceBlock8512Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8512XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8512+k):ℂ)).re ∧
      (xi (xiGridArgument (8512+k):ℂ)).re ≤ ((sourceBlock8512XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8512+k) _ _ _
    (sourceBlock8512PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8512_actual_enclosure k hk)
    (sourceBlock8512TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8512Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8512XiPair k).1 := by
  decide +kernel

theorem sourceBlock8512Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8512Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8512XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8512XiPair k)).2 ≤
      sourceBlock8512Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8512_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8512+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8512+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8512Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8512+k) (sourceBlock8512XiPair k) _
    (sourceBlock8512Xi_enclosure k hk) (sourceBlock8512Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8512Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first8544_bound (k : ℕ) (hk : k < 8544) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8512
  · exact sourceRoundedMidpoint_first8512_bound k h
  · have hsum : 8512+(k-8512) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8512_bound (k-8512) (by omega)

end ReciprocalXi
