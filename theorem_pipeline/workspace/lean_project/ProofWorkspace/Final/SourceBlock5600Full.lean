import ProofWorkspace.Final.SourceBlock5568Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5600DataFull
import ProofWorkspace.Final.EtaBlock5600Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5600XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5600+k) (sourceBlock5600PiPairs.getD k (0,0))
    (sourceEtaBatch5600Lower k, sourceEtaBatch5600Upper k)
    (sourceBlock5600TwoPairs.getD k (0,0))

theorem sourceBlock5600Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5600XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5600+k):ℂ)).re ∧
      (xi (xiGridArgument (5600+k):ℂ)).re ≤ ((sourceBlock5600XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5600+k) _ _ _
    (sourceBlock5600PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5600_actual_enclosure k hk)
    (sourceBlock5600TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5600Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5600XiPair k).1 := by
  decide +kernel

theorem sourceBlock5600Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5600Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5600XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5600XiPair k)).2 ≤
      sourceBlock5600Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5600_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5600+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5600+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5600Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5600+k) (sourceBlock5600XiPair k) _
    (sourceBlock5600Xi_enclosure k hk) (sourceBlock5600Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5600Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5632_bound (k : ℕ) (hk : k < 5632) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5600
  · exact sourceRoundedMidpoint_first5600_bound k h
  · have hsum : 5600+(k-5600) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5600_bound (k-5600) (by omega)

end ReciprocalXi
