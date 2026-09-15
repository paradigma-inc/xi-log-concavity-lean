import ProofWorkspace.Final.SourceBlock8960Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock8992DataFull
import ProofWorkspace.Final.EtaBlock8992Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock8992XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (8992+k) (sourceBlock8992PiPairs.getD k (0,0))
    (sourceEtaBatch8992Lower k, sourceEtaBatch8992Upper k)
    (sourceBlock8992TwoPairs.getD k (0,0))

theorem sourceBlock8992Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock8992XiPair k).1:ℝ) ≤ (xi (xiGridArgument (8992+k):ℂ)).re ∧
      (xi (xiGridArgument (8992+k):ℂ)).re ≤ ((sourceBlock8992XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (8992+k) _ _ _
    (sourceBlock8992PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch8992_actual_enclosure k hk)
    (sourceBlock8992TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock8992Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock8992XiPair k).1 := by
  decide +kernel

theorem sourceBlock8992Reciprocal_check : ∀ k : Fin 32,
    sourceBlock8992Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock8992XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock8992XiPair k)).2 ≤
      sourceBlock8992Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block8992_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((8992+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (8992+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock8992Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (8992+k) (sourceBlock8992XiPair k) _
    (sourceBlock8992Xi_enclosure k hk) (sourceBlock8992Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock8992Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first9024_bound (k : ℕ) (hk : k < 9024) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 8992
  · exact sourceRoundedMidpoint_first8992_bound k h
  · have hsum : 8992+(k-8992) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block8992_bound (k-8992) (by omega)

end ReciprocalXi
