import ProofWorkspace.Final.SourceBlock5408Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock5440DataFull
import ProofWorkspace.Final.EtaBlock5440Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock5440XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (5440+k) (sourceBlock5440PiPairs.getD k (0,0))
    (sourceEtaBatch5440Lower k, sourceEtaBatch5440Upper k)
    (sourceBlock5440TwoPairs.getD k (0,0))

theorem sourceBlock5440Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock5440XiPair k).1:ℝ) ≤ (xi (xiGridArgument (5440+k):ℂ)).re ∧
      (xi (xiGridArgument (5440+k):ℂ)).re ≤ ((sourceBlock5440XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (5440+k) _ _ _
    (sourceBlock5440PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch5440_actual_enclosure k hk)
    (sourceBlock5440TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock5440Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock5440XiPair k).1 := by
  decide +kernel

theorem sourceBlock5440Reciprocal_check : ∀ k : Fin 32,
    sourceBlock5440Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock5440XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock5440XiPair k)).2 ≤
      sourceBlock5440Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block5440_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((5440+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (5440+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock5440Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (5440+k) (sourceBlock5440XiPair k) _
    (sourceBlock5440Xi_enclosure k hk) (sourceBlock5440Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock5440Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first5472_bound (k : ℕ) (hk : k < 5472) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 5440
  · exact sourceRoundedMidpoint_first5440_bound k h
  · have hsum : 5440+(k-5440) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block5440_bound (k-5440) (by omega)

end ReciprocalXi
