import ProofWorkspace.Final.SourceBlock12480Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock12512DataFull
import ProofWorkspace.Final.EtaBlock12512Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock12512XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (12512+k) (sourceBlock12512PiPairs.getD k (0,0))
    (sourceEtaBatch12512Lower k, sourceEtaBatch12512Upper k)
    (sourceBlock12512TwoPairs.getD k (0,0))

theorem sourceBlock12512Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock12512XiPair k).1:ℝ) ≤ (xi (xiGridArgument (12512+k):ℂ)).re ∧
      (xi (xiGridArgument (12512+k):ℂ)).re ≤ ((sourceBlock12512XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (12512+k) _ _ _
    (sourceBlock12512PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch12512_actual_enclosure k hk)
    (sourceBlock12512TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock12512Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock12512XiPair k).1 := by
  decide +kernel

theorem sourceBlock12512Reciprocal_check : ∀ k : Fin 32,
    sourceBlock12512Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock12512XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock12512XiPair k)).2 ≤
      sourceBlock12512Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block12512_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((12512+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (12512+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock12512Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (12512+k) (sourceBlock12512XiPair k) _
    (sourceBlock12512Xi_enclosure k hk) (sourceBlock12512Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock12512Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first12544_bound (k : ℕ) (hk : k < 12544) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 12512
  · exact sourceRoundedMidpoint_first12512_bound k h
  · have hsum : 12512+(k-12512) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block12512_bound (k-12512) (by omega)

end ReciprocalXi
