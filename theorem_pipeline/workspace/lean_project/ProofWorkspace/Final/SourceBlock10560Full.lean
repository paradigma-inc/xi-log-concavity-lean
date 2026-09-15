import ProofWorkspace.Final.SourceBlock10528Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10560DataFull
import ProofWorkspace.Final.EtaBlock10560Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10560XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10560+k) (sourceBlock10560PiPairs.getD k (0,0))
    (sourceEtaBatch10560Lower k, sourceEtaBatch10560Upper k)
    (sourceBlock10560TwoPairs.getD k (0,0))

theorem sourceBlock10560Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10560XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10560+k):ℂ)).re ∧
      (xi (xiGridArgument (10560+k):ℂ)).re ≤ ((sourceBlock10560XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10560+k) _ _ _
    (sourceBlock10560PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10560_actual_enclosure k hk)
    (sourceBlock10560TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10560Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10560XiPair k).1 := by
  decide +kernel

theorem sourceBlock10560Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10560Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10560XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10560XiPair k)).2 ≤
      sourceBlock10560Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10560_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10560+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10560+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10560Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10560+k) (sourceBlock10560XiPair k) _
    (sourceBlock10560Xi_enclosure k hk) (sourceBlock10560Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10560Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10592_bound (k : ℕ) (hk : k < 10592) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10560
  · exact sourceRoundedMidpoint_first10560_bound k h
  · have hsum : 10560+(k-10560) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10560_bound (k-10560) (by omega)

end ReciprocalXi
