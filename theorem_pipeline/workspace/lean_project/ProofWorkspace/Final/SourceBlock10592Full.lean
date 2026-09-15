import ProofWorkspace.Final.SourceBlock10560Full
import ProofWorkspace.Final.SourceBlockAssemblyFull
import ProofWorkspace.Final.SourceBlock10592DataFull
import ProofWorkspace.Final.EtaBlock10592Full

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
noncomputable section
namespace ReciprocalXi

def sourceBlock10592XiPair (k : ℕ) : ℚ × ℚ :=
  sourceGridXiPair (10592+k) (sourceBlock10592PiPairs.getD k (0,0))
    (sourceEtaBatch10592Lower k, sourceEtaBatch10592Upper k)
    (sourceBlock10592TwoPairs.getD k (0,0))

theorem sourceBlock10592Xi_enclosure (k : ℕ) (hk : k < 32) :
    ((sourceBlock10592XiPair k).1:ℝ) ≤ (xi (xiGridArgument (10592+k):ℂ)).re ∧
      (xi (xiGridArgument (10592+k):ℂ)).re ≤ ((sourceBlock10592XiPair k).2:ℝ) :=
  sourceGridXi_enclosure (10592+k) _ _ _
    (sourceBlock10592PiPairs_eq ⟨k,hk⟩).symm
    (sourceEtaBatch10592_actual_enclosure k hk)
    (sourceBlock10592TwoPairs_eq ⟨k,hk⟩).symm

theorem sourceBlock10592Xi_positive_checked : ∀ k : Fin 32,
    0 < (sourceBlock10592XiPair k).1 := by
  decide +kernel

theorem sourceBlock10592Reciprocal_check : ∀ k : Fin 32,
    sourceBlock10592Midpoints.getD k 0-2/(10:ℚ)^120 ≤
      (sourceGridReciprocalPair (sourceBlock10592XiPair k)).1 ∧
    (sourceGridReciprocalPair (sourceBlock10592XiPair k)).2 ≤
      sourceBlock10592Midpoints.getD k 0+2/(10:ℚ)^120 := by
  decide +kernel

theorem sourceRoundedMidpoint_block10592_bound (k : ℕ) (hk : k < 32) :
    |(reciprocalTransform (((10592+k:ℕ):ℝ)/40)).re-
      (sourceRoundedMidpoint (10592+k):ℝ)| ≤ 2/(10:ℝ)^120 := by
  rw [←sourceBlock10592Midpoints_eq_array ⟨k,hk⟩]
  exact sourceGridMidpoint_actual_bound (10592+k) (sourceBlock10592XiPair k) _
    (sourceBlock10592Xi_enclosure k hk) (sourceBlock10592Xi_positive_checked ⟨k,hk⟩)
    (sourceBlock10592Reciprocal_check ⟨k,hk⟩)

theorem sourceRoundedMidpoint_first10624_bound (k : ℕ) (hk : k < 10624) :
    |(reciprocalTransform ((k:ℝ)/40)).re-(sourceRoundedMidpoint k:ℝ)| ≤
      2/(10:ℝ)^120 := by
  by_cases h : k < 10592
  · exact sourceRoundedMidpoint_first10592_bound k h
  · have hsum : 10592+(k-10592) = k := by omega
    simpa only [hsum] using sourceRoundedMidpoint_block10592_bound (k-10592) (by omega)

end ReciprocalXi
