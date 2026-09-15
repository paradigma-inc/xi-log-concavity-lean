import ProofWorkspace.Final.SourceBlock10432Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10464DataFull
import ProofWorkspace.Final.EtaBlock10464Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10464XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10464+k) (sourceBlock10464PiPairs.getD k (0,0))
    (sourceEtaBatch10464Lower k, sourceEtaBatch10464Upper k)
    (sourceBlock10464TwoPairs.getD k (0,0))

theorem sourceBlock10464Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10464XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10464+k):ℂ)).re ∧
      (xi (xiGridArgument (10464+k):ℂ)).re ≤ ((sourceBlock10464XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10464+k) _ _ _
    (sourceBlock10464PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10464_actual_enclosure k hk)
    (sourceBlock10464TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10464Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10464XiPair k).1 := by
  decide +kernel

theorem sourceBlock10464Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10464Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10464XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10464XiPair k)).2 ≤
      sourceBlock10464Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10464_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10464+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10464+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10464Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10464+k) (sourceBlock10464XiPair k) _
    (sourceBlock10464Xi_enclosure k hk) (sourceBlock10464Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10464Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10496_bound (k : ℕ) (hk : k < 10496) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10464
  · exact sourceRoundedMidpoint_first10464_bound k h
  · have hsum : 10464+(k-10464) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10464_bound (k-10464) (by omega)

end ReciprocalXi
